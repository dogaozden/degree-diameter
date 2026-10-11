import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe families.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW family: bipartite Haar (Cayley-type) graphs over groups Z_m x| Z_k2.
#
# Vertices a_g and b_h for g, h in G (|G| = G). Connection set S of d distinct
# elements: a_g ~ b_{g*s} for s in S. Each side has degree d, bipartite, and
# the left action of G is an automorphism group transitive on each side, so
# the diameter check reduces to two BFS runs (from a_identity and b_identity).
# Search: simulated annealing over S, minimising unreached (vertex, source) pairs.
# ----------------------------------------------------------------------------

def _haar_tables(m, k2, r):
    """Return (G, M, inv): M[g, h] = g*h, inv[s] = s^{-1}; identity has index 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=0)
    return G, M, inv


def _sample_haar_group(G_target, rng):
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12])
        m = max(2, -(-G_target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _haar_cost(NA, NB, G, D):
    """Total unreached (vertex, source) pairs for sources a_0 and b_0 within distance D."""
    total = 0
    for start in (0, 1):
        R = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        R[start][0] = True
        front = np.array([0], dtype=np.int64)
        side = start
        for _ in range(D):
            tbl = NB if side == 0 else NA
            mark = np.zeros(G, dtype=bool)
            mark[tbl[front].ravel()] = True
            other = 1 - side
            newm = mark & ~R[other]
            if not newm.any():
                break
            R[other] |= newm
            front = np.flatnonzero(newm)
            side = other
        total += 2 * G - int(R[0].sum()) - int(R[1].sum())
    return total


def _haar_anneal(d, D, G, M, inv, rng, deadline, iters):
    """Return a connection set S (list of d distinct group indices) with zero cost, or None."""
    S = rng.sample(range(G), d)

    def cost_of(S):
        Sa = np.array(S, dtype=np.int64)
        NB = M[:, Sa]
        NA = M[:, inv[Sa]]
        return _haar_cost(NA, NB, G, D)

    cur = cost_of(S)
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = cost_of(S)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            S[i] = old
    return S if cur == 0 else None


def _haar_phase(d, D, rng, phase_deadline, st, consider):
    while time.monotonic() < phase_deadline:
        target = st["n"] // 2 + 1 + rng.randrange(0, 3)
        g = _sample_haar_group(max(target, d + 1), rng)
        if g is None:
            continue
        m, k2, r = g
        G, M, inv = _haar_tables(m, k2, r)
        if G < d + 1 or 2 * G <= st["n"]:
            continue
        att_deadline = min(phase_deadline, time.monotonic() + 4.0)
        S = _haar_anneal(d, D, G, M, inv, rng, att_deadline, 8000)
        if S is not None:
            NB = M[:, np.array(S, dtype=np.int64)]
            edges = [(gg, G + int(NB[gg, j])) for gg in range(G) for j in range(d)]
            consider(2 * G, edges)


# ----------------------------------------------------------------------------
# Fallback family: bi-Cayley lifts over semidirect products with k blocks
# (the parent's annealing search, kept as a safety net).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
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


def _bicayley_phase(d, D, rng, phase_deadline, st, consider):
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < phase_deadline:
        k = pick_k()
        base = st["n"] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= st["n"]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, phase_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Greedy pair insertion (parent's extension step).
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


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
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
            fails = 0
        else:
            fails += 1
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    st = {"n": fallback[0], "e": fallback[1]}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"] = n
            st["e"] = e

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return st["n"], st["e"]

    if D >= 4 and time.monotonic() < start + 0.3 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return st["n"], st["e"]

    # Bold new family: bipartite Haar graphs over groups, annealed on S.
    if D >= 3 and d >= 2:
        _haar_phase(d, D, rng, start + 0.55 * budget, st, consider)

    # Fallback family: bi-Cayley lift search, using the remaining time.
    _bicayley_phase(d, D, rng, start + 0.85 * budget, st, consider)

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(st["n"], st["e"], d, D, rng, deadline)
        if n2 > st["n"]:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(st["n"], st["e"], d, D):
        return fallback
    return st["n"], st["e"]
