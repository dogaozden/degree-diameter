import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (as in the parent).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages, layer swaps and defect-targeted moves."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition, greedy pair insertion (validity-checked).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _pick_matching(edges, color, d, rng):
    """Pick d-1 edges with pairwise distinct A-ends and distinct B-ends. Returns list of (a, b) or None."""
    order = list(range(len(edges)))
    rng.shuffle(order)
    chosen = []
    used_a, used_b = set(), set()
    for t in order:
        if len(chosen) == d - 1:
            break
        u, v = edges[t]
        a, b = (u, v) if color[u] == 0 else (v, u)
        if a in used_a or b in used_b:
            continue
        chosen.append(t)
        used_a.add(a)
        used_b.add(b)
    if len(chosen) < d - 1:
        return None
    return [edges[t] if color[edges[t][0]] == 0 else (edges[t][1], edges[t][0]) for t in chosen], set(chosen)


def _extend(n, edges, d, D, rng, deadline):
    """Greedy pair insertion, accepting only steps that pass lib.is_valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        res = _pick_matching(edges, color, d, rng)
        if res is None:
            break
        pairs, chosen = res
        x, y = n, n + 1
        cand = [e for t, e in enumerate(edges) if t not in chosen]
        for a, b in pairs:
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


def _insert_pair(n, edges, color, d, rng):
    """Insert two vertices keeping all degrees = d (validity not checked). Returns (n+2, edges, color) or None."""
    res = _pick_matching(edges, color, d, rng)
    if res is None:
        return None
    pairs, chosen = res
    x, y = n, n + 1
    cand = [e for t, e in enumerate(edges) if t not in chosen]
    for a, b in pairs:
        cand.append((x, b))
        cand.append((y, a))
    cand.append((x, y))
    return n + 2, cand, color + [0, 1]


# ----------------------------------------------------------------------------
# NEW: unstructured 2-switch annealing that minimises bad pairs on a regular
# bipartite graph. Degrees and bipartition are preserved by each switch.
# ----------------------------------------------------------------------------

def _switch_anneal(n, edges, d, D, rng, deadline):
    """Anneal bipartite 2-switches to drive bad_pairs to 0. Returns valid edges or None."""
    L = [(u, v) for u, v in edges]  # (a, b): a is colour-0 endpoint
    S = set(L)
    pos = {e: i for i, e in enumerate(L)}
    cost = lib.bad_pairs(n, L, D)
    if cost == 0:
        return L if lib.is_valid(n, L, d, D) else None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(L)
    it = 0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        if it % 16 == 0:
            frac = (time.monotonic() - t0) / span
            temp = max(0.15, 2.0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = L[i]
        a2, b2 = L[j]
        if a1 == a2 or b1 == b2:
            continue
        e1, e2 = (a1, b2), (a2, b1)
        if e1 in S or e2 in S:
            continue
        # apply
        S.discard(L[i]); S.discard(L[j])
        del pos[L[i]]; del pos[L[j]]
        L[i], L[j] = e1, e2
        S.add(e1); S.add(e2)
        pos[e1] = i; pos[e2] = j
        c2 = lib.bad_pairs(n, L, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            # revert
            S.discard(e1); S.discard(e2)
            del pos[e1]; del pos[e2]
            L[i], L[j] = a1, b1
            L[j] = (a2, b2)
            S.add((a1, b1)); S.add((a2, b2))
            pos[(a1, b1)] = i; pos[(a2, b2)] = j
    if cost == 0 and lib.is_valid(n, L, d, D):
        return L
    return None


def _grow_by_anneal(n, edges, d, D, rng, deadline):
    """Repeatedly insert a pair and anneal it back to validity; keep only successes."""
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    best = (n, list(edges))
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        res = _insert_pair(best[0], best[1], color, d, rng)
        if res is None:
            break
        n2, e2, c2 = res
        sub = time.monotonic() + max(3.0, 0.5 * remaining)
        out = _switch_anneal(n2, e2, d, D, rng, min(sub, deadline))
        if out is None:
            break
        best = (n2, out)
        color = c2
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + 0.5 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley lift search (bandit over base sizes k).
    # Shorter for D >= 5 so the new annealing phase gets real time.
    lift_frac = 0.5 if D >= 5 else 0.8
    search_deadline = start + lift_frac * budget

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: validity-checked greedy insertion.
    ext_deadline = start + (0.6 * budget if D >= 5 else 0.85 * budget)
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, ext_deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    # Phase 3 (new, D >= 5): degree-preserving insertion + bad-pair annealing.
    if D >= 5:
        try:
            n3, e3 = _grow_by_anneal(best_n, best[1], d, D, rng, start + budget)
            if n3 > best_n:
                consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
