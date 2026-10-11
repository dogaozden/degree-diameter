import math
import random
import time

import numpy as np

import lib


def _largest_pp_le(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _conic_arc(q):
    """Conic (plus nucleus for even q) as a point-index set in PG(2, q)."""
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy_arc(m, s, pl, lp, rng):
    """Randomized greedy S with every line holding <= s points of S and every point on <= s lines of S."""
    order = list(range(m))
    rng.shuffle(order)
    cl = [0] * m
    cp = [0] * m
    S = []
    for P in order:
        if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
            S.append(P)
            for L in pl[P]:
                cl[L] += 1
            for Q in lp[P]:
                cp[Q] += 1
    return S


def _arc_base(d, rng):
    """PG(2,q) incidence with q the largest prime power <= d-1, extended by an arc of A and B vertices.

    Returns (n, edges, colour list) or None. Colour 0 = point side, 1 = line side.
    """
    q = _largest_pp_le(d - 1)
    if q is None:
        return None
    n0, E0 = lib.projective_plane_incidence(q)
    m = n0 // 2
    col0 = [0] * m + [1] * m
    s = d - q - 1
    if s <= 0:
        return n0, E0, col0

    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in E0:
        pl[u].append(v - m)
        lp[v - m].append(u)

    def ok(S):
        cl = [0] * m
        cp = [0] * m
        for P in S:
            for L in pl[P]:
                cl[L] += 1
            for Q in lp[P]:
                cp[Q] += 1
        return max(cl) <= s and max(cp) <= s

    cands = []
    conic = _conic_arc(q)
    if ok(conic):
        cands.append(conic)
    for _ in range(30):
        cands.append(_greedy_arc(m, s, pl, lp, rng))
    S = max(cands, key=len, default=[])
    if not S:
        return n0, E0, col0

    k = len(S)
    n = 2 * m + 2 * k
    E = list(E0)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    col = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, col


def _reach_bad(adj, D):
    """Number of unordered vertex pairs at distance > D, from a float32 adjacency matrix."""
    n = adj.shape[0]
    M = adj.copy()
    np.fill_diagonal(M, 1.0)
    R = M
    for _ in range(D - 1):
        R = ((R @ M) > 0).astype(np.float32)
    return (n * n - int(np.count_nonzero(R))) // 2


def _set(adj, deg, u, v, val):
    """Set edge u-v to val (0 or 1), keeping degrees in sync."""
    if adj[u, v] == val:
        return
    adj[u, v] = val
    adj[v, u] = val
    delta = 1 if val else -1
    deg[u] += delta
    deg[v] += delta


def _export(adj):
    r, c = np.nonzero(np.triu(adj, 1))
    return list(zip(r.tolist(), c.tolist()))


def _grow(adj, col, deg):
    """Append one new vertex on each side (isolated)."""
    n = adj.shape[0]
    adj2 = np.zeros((n + 2, n + 2), dtype=np.float32)
    adj2[:n, :n] = adj
    return adj2, col + [0, 1], deg + [0, 0]


def _repair(n, edges, col, d, D, deadline, rng):
    """Simulated annealing on bad-pair count, growing the graph by one vertex pair each time it reaches cost 0."""
    adj = np.zeros((n, n), dtype=np.float32)
    for u, v in edges:
        adj[u, v] = 1.0
        adj[v, u] = 1.0
    deg = [int(x) for x in adj.sum(axis=1)]
    col = list(col)
    S0 = [v for v in range(n) if col[v] == 0]
    S1 = [v for v in range(n) if col[v] == 1]
    cost = _reach_bad(adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05
    best = None

    while time.monotonic() < deadline:
        if cost == 0:
            e = _export(adj)
            if not lib.is_valid(n, e, d, D):
                break
            best = (n, e)
            adj, col, deg = _grow(adj, col, deg)
            n += 2
            S0 = [v for v in range(n) if col[v] == 0]
            S1 = [v for v in range(n) if col[v] == 1]
            cost = _reach_bad(adj, D)
            continue

        frac = (time.monotonic() - t0) / span
        T = T0 * (T1 / T0) ** min(1.0, frac)
        a = S0[rng.randrange(len(S0))]
        b = S1[rng.randrange(len(S1))]
        if adj[a, b] > 0:
            continue
        rem = []
        if deg[a] >= d:
            nb = np.flatnonzero(adj[a])
            rem.append((a, int(nb[rng.randrange(len(nb))])))
        if deg[b] >= d:
            nb = np.flatnonzero(adj[:, b])
            rem.append((int(nb[rng.randrange(len(nb))]), b))
        for u, v in rem:
            _set(adj, deg, u, v, 0)
        _set(adj, deg, a, b, 1)
        new = _reach_bad(adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _set(adj, deg, a, b, 0)
            for u, v in rem:
                _set(adj, deg, u, v, 1)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    moore = lib.moore_bound(d, D)

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]
    best_col = [0] * d + [1] * d

    if D >= 3:
        base = _arc_base(d, rng)
        if base is not None:
            n, E, col = base
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_e, best_col = n, E, col

    if best_n < moore and time.monotonic() < deadline:
        res = _repair(best_n, best_e, best_col, d, D, deadline, rng)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
