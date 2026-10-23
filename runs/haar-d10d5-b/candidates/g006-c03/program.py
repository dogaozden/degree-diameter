"""Voltage-lift search for the bipartite degree-diameter problem at diameter 5 (numpy only).

This version replaces the Haar-graph construction for the target case with a different one: a lift of a small
bipartite base multigraph with a asymmetric voltage pattern over a non-abelian group.

Construction. The base has a A-vertices and a B-vertices, and each vertex carries d darts. The darts are the union of
d random perfect matchings between A and B, so every base vertex has degree d. A dart (u, v, g) joins (u, x) to
(v, x*g) for every x in G. The lift has 2a|G| vertices, is bipartite, and is d-regular if voltages on parallel darts
are distinct.

Why one BFS per base vertex suffices. Left multiplication by h maps (u, x) to (u, h x) and is an automorphism of the
lift. Every fibre is therefore vertex-transitive, and the diameter equals the maximum eccentricity of the 2a base
vertices (u, e). The cost is the number of base-vertex-to-vertex pairs at distance more than D, and it is 0 exactly
when the lift has diameter at most D.

Search. Simulated annealing over the voltages, with restarts. Each step changes one voltage and re-runs 2a BFS
passes. Groups are semidirect products Z_m x| Z_k with order just above the record threshold: for a = 2 the order is
at least 1001 (4004 vertices), for a = 3 the order is at least 667 (4002 vertices).

Safety. Every returned graph is checked with lib.is_valid. If nothing valid is found, the program falls back to the
valid Haar graph of order 1791 (3582 vertices), and then to a trivial valid graph. Other cases return instantly.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def meta_candidates(lo, hi):
    """(N, m, k, lam) for every semidirect product Z_m x| Z_k with N = m*k in [lo, hi] and lam != 1 (nonabelian)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= 2:
                        break
    return out


# ------------------------------------------------------------------------------- voltage lift search

def _conflict(darts, i, g):
    """True if putting voltage g on dart i would duplicate another dart on the same base pair."""
    u, v, _ = darts[i]
    for j, (uu, vv, gg) in enumerate(darts):
        if j != i and uu == u and vv == v and gg == g:
            return True
    return False


def _init_darts(a, d, N, rng):
    """d random perfect matchings between the a A-vertices and the a B-vertices, with random distinct voltages."""
    darts = []
    for _ in range(d):
        p = rng.permutation(a)
        for u in range(a):
            darts.append([u, int(p[u]), 0])
    for i in range(len(darts)):
        g = int(rng.integers(N))
        while _conflict(darts, i, g):
            g = int(rng.integers(N))
        darts[i][2] = g
    return darts


def _copy(darts):
    return [list(x) for x in darts]


def lift_adj(MT, inv, a, darts, d):
    """Adjacency (n, d) of the lift. A-vertex (u, x) has id u*N + x; B-vertex (v, y) has id a*N + v*N + y."""
    N = MT.shape[0]
    n = 2 * a * N
    Adj = np.empty((n, d), dtype=np.int64)
    slotA = [0] * a
    slotB = [0] * a
    for u, v, g in darts:
        j = slotA[u]
        slotA[u] += 1
        Adj[u * N:(u + 1) * N, j] = a * N + v * N + MT[:, g]
        j2 = slotB[v]
        slotB[v] += 1
        base = a * N + v * N
        Adj[base:base + N, j2] = u * N + MT[:, inv[g]]
    return Adj


def lift_cost(Adj, a, N, D):
    """Number of (base vertex, vertex) pairs at distance more than D. Zero iff the lift has diameter at most D."""
    n = Adj.shape[0]
    total = 0
    sources = [u * N for u in range(a)] + [a * N + v * N for v in range(a)]
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = Adj[fr].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            fr = nb
        total += n - int(seen.sum())
    return total


def anneal(MT, inv, a, d, D, deadline, rng):
    """Anneal the voltages. Returns (best cost, best darts)."""
    N = MT.shape[0]
    darts = _init_darts(a, d, N, rng)
    cur = lift_cost(lift_adj(MT, inv, a, darts, d), a, N, D)
    best_c, best_d = cur, _copy(darts)
    T, since = 1.5, 0
    while best_c > 0 and time.monotonic() < deadline:
        if since > 1500:
            darts = _init_darts(a, d, N, rng)
            cur = lift_cost(lift_adj(MT, inv, a, darts, d), a, N, D)
            T, since = 1.5, 0
            if cur < best_c:
                best_c, best_d = cur, _copy(darts)
            continue
        i = int(rng.integers(len(darts)))
        g = int(rng.integers(N))
        if g == darts[i][2] or _conflict(darts, i, g):
            since += 1
            continue
        old = darts[i][2]
        darts[i][2] = g
        c = lift_cost(lift_adj(MT, inv, a, darts, d), a, N, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if c < best_c:
                best_c, best_d = c, _copy(darts)
                since = 0
            else:
                since += 1
        else:
            darts[i][2] = old
            since += 1
        T = max(0.2, T * 0.999)
    return best_c, best_d


def lift_edges(Adj, a, N):
    """Edge list of the lift: each A-vertex contributes its d neighbours."""
    return [(i, j) for i, row in enumerate(Adj[:a * N].tolist()) for j in row]


# --------------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(x), int(N + y)) for s in S for x, y in zip(g, MT[s])]


def fallback_haar(d, D):
    """Valid Haar graph of order 1791 (3582 vertices) for the target case, else the trivial graph."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------------ driver

def solve(d, D, seed, time_limit):
    """Search lifts over several nonabelian groups, keep the largest valid graph."""
    t0 = time.monotonic()
    budget = min(float(time_limit), 60.0)
    deadline = t0 + max(2.0, 0.8 * budget - 3.0)
    rng = np.random.default_rng(seed)

    pools = {2: meta_candidates(1001, 1040), 3: meta_candidates(667, 690)}
    ptr = {2: 0, 3: 0}
    best = None
    turn = 0
    while time.monotonic() < deadline - 0.5:
        a = 2 if turn % 3 != 2 else 3
        turn += 1
        if ptr[a] >= len(pools[a]):
            a = 3 if a == 2 else 2
            if ptr[a] >= len(pools[a]):
                break
        N, m, k, lam = pools[a][ptr[a]]
        ptr[a] += 1
        try:
            MT, inv = group_meta(m, k, lam)
            end = min(deadline, time.monotonic() + 8.0)
            c, darts = anneal(MT, inv, a, d, D, end, rng)
            if c == 0:
                Adj = lift_adj(MT, inv, a, darts, d)
                n = 2 * a * N
                edges = lift_edges(Adj, a, N)
                if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
        except Exception:
            continue
    return best


def build(d, D, seed, time_limit):
    try:
        if (d, D) != TARGET:
            return trivial(d, D)
        g = solve(d, D, seed, time_limit)
        if g is not None:
            return g
        return fallback_haar(d, D)
    except Exception:
        return trivial(d, D)
