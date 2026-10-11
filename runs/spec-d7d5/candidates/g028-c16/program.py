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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (phase 1, unchanged).
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
                r = None
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
    Ts = np.ascontiguousarray(M.T)
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
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
                if cost < best_cost:
                    best_cost, last_improve = cost, t
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
            if cost < best_cost:
                best_cost, last_improve = cost, t
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
# Phase 2 (new): direct annealing over simple d-regular bipartite graphs.
#
# Vertices: A = 0..m-1, B = m..2m-1. adj[v, l] is the l-th neighbour of v.
# Moves: bipartite double-edge switch (a1-b1, a2-b2 -> a1-b2, a2-b1).
# Cost: unordered vertex pairs at distance > D, from bit-packed BFS.
# When cost reaches 0, the graph is recorded, then grown by two vertices
# (one per side) by rerouting d edges, and annealing repairs the diameter.
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _packed_reach(adj, n, D):
    W = (n + 63) >> 6
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(adj.shape[1]):
            new |= reach[adj[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _bad_pairs(adj, n, D):
    reach = np.ascontiguousarray(_packed_reach(adj, n, D))
    total = int(_POP16[reach.view(np.uint16)].sum())
    return (n * n - total) // 2


def _haar_adj(m, d, S):
    adj = np.empty((2 * m, d), dtype=np.int64)
    a = np.arange(m, dtype=np.int64)
    for l, s in enumerate(S):
        adj[:m, l] = m + (a + s) % m
        adj[m:, l] = (a - s) % m
    return adj


def _matrix(adj, m):
    M = np.zeros((m, m), dtype=bool)
    d = adj.shape[1]
    rows = np.repeat(np.arange(m), d)
    M[rows, adj[:m].ravel() - m] = True
    return M


def _slot(adj, v, w):
    return int(np.flatnonzero(adj[v] == w)[0])


def _switch(adj, M, m, a1, a2, b1, b2):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1 (all four must exist beforehand)."""
    adj[a1, _slot(adj, a1, b1)] = b2
    adj[a2, _slot(adj, a2, b2)] = b1
    adj[b1, _slot(adj, b1, a1)] = a2
    adj[b2, _slot(adj, b2, a2)] = a1
    M[a1, b1 - m] = False
    M[a2, b2 - m] = False
    M[a1, b2 - m] = True
    M[a2, b1 - m] = True


def _edges(adj, m):
    d = adj.shape[1]
    return [(a, int(adj[a, l])) for a in range(m) for l in range(d)]


def _grow(adj, m, rng):
    """Add one A vertex and one B vertex; returns (new_m, new_adj) or None."""
    d = adj.shape[1]
    edges = _edges(adj, m)
    order = list(range(len(edges)))
    chosen = None
    for _ in range(200):
        rng.shuffle(order)
        ua, ub, pick = set(), set(), []
        for e in order:
            a, b = edges[e]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            pick.append(e)
            if len(pick) == d:
                break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    chosen_set = set(chosen)
    new_m = m + 1
    newA = m
    newB = 2 * new_m - 1
    ne = []
    for e, (a, x) in enumerate(edges):
        if e not in chosen_set:
            ne.append((a, x + 1))
    for e in chosen:
        a, x = edges[e]
        ne.append((a, newB))
        ne.append((newA, x + 1))
    nadj = np.full((2 * new_m, d), -1, dtype=np.int64)
    fill = [0] * (2 * new_m)
    for u, v in ne:
        if fill[u] >= d or fill[v] >= d:
            return None
        nadj[u, fill[u]] = v
        fill[u] += 1
        nadj[v, fill[v]] = u
        fill[v] += 1
    if any(f != d for f in fill):
        return None
    return new_m, nadj


def _sa_grow(D, m, adj, rng, deadline, found):
    d = adj.shape[1]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    M = _matrix(adj, m)
    cost = _bad_pairs(adj, 2 * m, D)
    T0 = max(2.0, 0.05 * cost)
    T1 = 0.3
    while True:
        now = time.monotonic()
        if now >= deadline:
            return
        if cost == 0:
            found(2 * m, _edges(adj, m))
            grown = _grow(adj, m, rng)
            if grown is None:
                return
            m, adj = grown
            M = _matrix(adj, m)
            cost = _bad_pairs(adj, 2 * m, D)
            continue
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        a1 = rng.randrange(m)
        a2 = rng.randrange(m)
        if a1 == a2:
            continue
        b1 = int(adj[a1, rng.randrange(d)])
        b2 = int(adj[a2, rng.randrange(d)])
        if b1 == b2 or M[a1, b2 - m] or M[a2, b1 - m]:
            continue
        _switch(adj, M, m, a1, a2, b1, b2)
        c2 = _bad_pairs(adj, 2 * m, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _switch(adj, M, m, a1, a2, b2, b1)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + 0.4 * budget          # end of phase 1 (lift search)
    sa_deadline = start + budget             # end of phase 2 (annealing)
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bandit over lift base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: annealing on d-regular bipartite graphs, grow-and-repair.
    if D >= 3 and d >= 3 and time.monotonic() < sa_deadline:
        m0 = best_n // 2 + 1
        if m0 >= d:
            S = rng.sample(range(m0), d)
            adj0 = _haar_adj(m0, d, S)
            try:
                _sa_grow(D, m0, adj0, rng, sa_deadline, consider)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
