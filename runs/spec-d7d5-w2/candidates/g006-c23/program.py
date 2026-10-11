import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Exact constructions (used only where they are known to be optimal or strong).
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
# NEW PRIMARY FAMILY: bipartite Cayley graphs over groups of order G.
#
# Vertices A_g = g and B_g = G + g. Edge A_g ~ B_{g*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so distances from (A, e) and (B, e)
# determine the diameter. Search over the connection set S by simulated
# annealing, minimising the number of vertices unreached within D steps.
# Groups are semidirect products Z_m x| Z_k (element a*k+b).
# ----------------------------------------------------------------------------

def _semidirect_mul(m, k, r):
    """Multiplication table M[x, y] for Z_m x| Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return M


def _cayley_groups(G, rng, count):
    """Candidate (m, k, r) with m*k = G: the cyclic group first, then random semidirect products."""
    out = [(G, 1, 1)]
    divs = [k for k in range(2, G) if G % k == 0 and G // k >= 3]
    tries = 0
    while divs and len(out) < count and tries < 40:
        tries += 1
        k = rng.choice(divs)
        m = G // k
        r = m - 1 if k == 2 else rng.randrange(2, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            out.append((m, k, r))
    return out


def _cayley_cost(MT, inv, S, G, D):
    """Number of (start, vertex) pairs unreached within D steps, for starts A_e and B_e."""
    invS = [int(inv[s]) for s in S]
    unreached = 0
    for side in (0, 1):
        vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        vis[side][0] = True
        front = vis[side].copy()
        cur = side
        for _ in range(D):
            nxt = np.zeros(G, dtype=bool)
            if cur == 0:
                for s in S:
                    nxt[MT[s]] |= front          # A_g -> B_{g*s}
            else:
                for t in invS:
                    nxt[MT[t]] |= front          # B_h -> A_{h*s^-1}
            other = 1 - cur
            nxt &= ~vis[other]
            vis[other] |= nxt
            front = nxt
            cur = other
            if not front.any():
                break
        unreached += 2 * G - int(vis[0].sum()) - int(vis[1].sum())
    return unreached


def _cayley_search(MT, inv, G, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d. Returns S or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    cost = _cayley_cost(MT, inv, S, G, D)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _cayley_cost(MT, inv, S2, G, D)
        temp = max(0.3, 5.0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            S, cost = S2, c2
    return S if cost == 0 else None


def _cayley_edges(M, S):
    """Return (2G, edges) for the bipartite Cayley graph with connection set S."""
    G = M.shape[0]
    edges = []
    for s in S:
        col = M[:, s]
        for g in range(G):
            edges.append((g, G + int(col[g])))
    return 2 * G, edges


def _cayley_phase(d, D, best_n, rng, deadline):
    """Repeatedly try to find a valid Cayley graph slightly larger than the current best."""
    best = None
    best_G = max(best_n // 2, d)
    while time.monotonic() < deadline:
        G = best_G + 1 + rng.randrange(6)
        for (m, k, r) in _cayley_groups(G, rng, 3):
            if time.monotonic() >= deadline:
                break
            M = _semidirect_mul(m, k, r)
            MT = np.ascontiguousarray(M.T)
            inv = np.argmax(M == 0, axis=1)
            S = _cayley_search(MT, inv, G, d, D, rng, deadline, 1500)
            if S is not None:
                n2, e2 = _cayley_edges(M, S)
                if lib.is_valid(n2, e2, d, D):
                    best = (n2, e2)
                    best_G = G
                    break
    return best


# ----------------------------------------------------------------------------
# Secondary family: bi-Cayley lifts over Z_m x| Z_k2 with k base vertices per side.
# ----------------------------------------------------------------------------

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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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
    """Simulated annealing over voltages and layer swaps. Returns (n, edges) or None."""
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


def _bicayley_phase(d, D, best_n, rng, deadline):
    """Bandit-driven search over bi-Cayley lifts; returns the best (n, edges) found or None."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    cur_n = best_n
    best = None

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = cur_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= cur_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            wins[k] += 1
            cur_n, best = res[0], res
    return best


# ----------------------------------------------------------------------------
# Greedy pair insertion: grows the order by 2 per accepted step, keeps d-regularity.
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


def _extend(n, edges, d, D, rng, deadline):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
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
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for calibration-style cases.
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

    # Phase 1: bipartite Cayley search (new family), about 55% of the budget.
    try:
        cay = _cayley_phase(d, D, best[0], rng, start + 0.55 * budget)
        if cay is not None:
            consider(cay[0], cay[1])
    except Exception:
        pass

    # Phase 2: bi-Cayley lift search, up to 80% of the budget.
    try:
        bi = _bicayley_phase(d, D, best[0], rng, start + 0.80 * budget)
        if bi is not None:
            consider(bi[0], bi[1])
    except Exception:
        pass

    # Phase 3: greedy pair insertion on the best graph.
    try:
        n2, e2 = _extend(best[0], best[1], d, D, rng, deadline)
        if n2 > best[0]:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
