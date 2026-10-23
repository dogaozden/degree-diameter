"""Lift search for the bipartite degree-diameter problem at (d, D) = (10, 5), numpy only.

This version replaces the single-vertex Haar construction with a 2+2 base multigraph lift over a
non-abelian metacyclic group G = Z_m x| Z_k, of order N in [1001, 1100]. The vertices are A_a x G
(a = 0, 1) and B_b x G (b = 0, 1), giving n = 4N vertices. Each base pair (a, b) carries a set of
c_ab distinct voltages g, with c = [[p, 10-p], [10-p, p]], so every vertex has degree exactly 10.
The dart (a, b, g) joins (a, x) to (b, x*g) for every x in G.

Left multiplication by G is an automorphism that fixes each base class, so the lift has diameter at
most 5 iff the four identity vertices (one per base class) each reach every vertex within 5 steps.
The search anneals the voltage sets with a cost equal to the number of uncovered vertices from those
four sources, using a fast numpy BFS. Any candidate with cost 0 is verified with lib.is_valid.

Fallbacks: the parent's valid Haar graph (order 1791, 3582 vertices), then a small always-valid graph.
Other (d, D) cases use the small always-valid construction, so the calibration case stays at its record.
"""
import math
import time

import numpy as np

import lib

DEG = 10
DIAM = 5
TARGET = (10, 5)
TEMP = 2.0
PATIENCE = 3000


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inv) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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


def group_options(N):
    """Non-abelian metacyclic groups Z_m x| Z_k of order N (lam != 1, so the action is nontrivial)."""
    opts = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) != 1:
                continue
            if pow(lam, k, m) != 1 % m:
                continue
            opts.append((m, k, lam))
            if len(opts) >= 40:
                return opts
    return opts


# ------------------------------------------------------------------------------------------ lift graph

def lift_adj(MT, inv, N, sets):
    """Adjacency (4N x DEG) of the base-2+2 lift. A_a vertex x is a*N + x, B_b vertex y is 2N + b*N + y.
    sets[a][b] lists the voltages of darts A_a -> B_b. Each A row gets DEG darts, and each B column gets DEG."""
    n = 4 * N
    adj = np.empty((n, DEG), dtype=np.int64)
    for a in range(2):
        slot = 0
        for b in range(2):
            for g in sets[a][b]:
                adj[a * N:(a + 1) * N, slot] = 2 * N + b * N + MT[:, g]
                slot += 1
    for b in range(2):
        slot = 0
        for a in range(2):
            for g in sets[a][b]:
                adj[2 * N + b * N:2 * N + (b + 1) * N, slot] = a * N + MT[:, inv[g]]
                slot += 1
    return adj


def ball_cost(adj, N):
    """Uncovered vertices, summed over the four base identities, within distance DIAM. 0 means diameter <= DIAM."""
    n = 4 * N
    cost = 0
    for s in (0, N, 2 * N, 3 * N):
        vis = np.zeros(n, dtype=bool)
        vis[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(DIAM):
            nb = np.unique(adj[fr])
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            vis[nb] = True
            fr = nb
        cost += n - int(vis.sum())
    return cost


def anneal(N, rng, deadline, opts):
    """Random restarts plus annealing over the voltage sets. Returns (MT, inv, sets) with cost 0, or None."""
    while time.monotonic() < deadline:
        m, k, lam = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        p = int(rng.integers(3, 8))  # 3..7, so every dart count is positive
        counts = [[p, DEG - p], [DEG - p, p]]
        sets = [[[int(x) for x in rng.choice(N, counts[a][b], replace=False)] for b in range(2)] for a in range(2)]
        cur = ball_cost(lift_adj(MT, inv, N, sets), N)
        stale = 0
        while cur > 0 and stale < PATIENCE and time.monotonic() < deadline:
            a = int(rng.integers(2))
            b = int(rng.integers(2))
            row = sets[a][b]
            i = int(rng.integers(len(row)))
            g = int(rng.integers(N))
            if g in row:
                stale += 1
                continue
            old = row[i]
            row[i] = g
            c2 = ball_cost(lift_adj(MT, inv, N, sets), N)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                cur = c2
            else:
                row[i] = old
            stale = 0 if delta < 0 else stale + 1
        if cur == 0:
            return MT, inv, sets
    return None


def search_lift(seed, time_limit):
    """Scan group orders N = 1001..1100 in ascending order and keep the largest verified valid lift."""
    t0 = time.monotonic()
    end = t0 + 0.6 * time_limit
    rng = np.random.default_rng(seed)
    best = None
    for N in range(1001, 1101):
        now = time.monotonic()
        remaining = end - now
        if remaining < 1.0:
            break
        opts = group_options(N)
        if not opts:
            continue
        slice_end = now + min(remaining, 5.0)
        found = anneal(N, rng, slice_end, opts)
        if found is None:
            continue
        MT, inv, sets = found
        adj = lift_adj(MT, inv, N, sets)
        n = 4 * N
        edges = [(u, int(v)) for u in range(2 * N) for v in adj[u].tolist()]
        if lib.is_valid(n, edges, DEG, DIAM) and (best is None or n > best[0]):
            best = (n, edges)
    return best


# ------------------------------------------------------------------------------- fallback helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]  # valid Haar graph, order 1791


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = search_lift(seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
