import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-orbit Haar graphs over finite groups.
#
# For a group G (order G_n, multiplication table M) and a connection set S of size d,
# the Haar graph has A_g ~ B_{g s} for s in S, giving 2*G_n vertices and degree d.
# Left multiplication is an automorphism, so the diameter is at most D iff every vertex
# is within distance D of A_1 and of B_1. Normalising 0 (identity) into S loses nothing.
#
# Search: for each group order G (ascending), sample semidirect groups Z_m x| Z_k2,
# then run simulated annealing on S, minimising the number of unreached (source, vertex)
# pairs. Each cost evaluation is a vectorised BFS over 2G vertices, so the search is cheap.
# Every accepted graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k2, r):
    """Multiplication table M[x, y] of Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return M


def _group_candidates(G, rng):
    """Shuffled list of (m, k2, r) with m * k2 = G giving a valid semidirect product."""
    out = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m == 1:
            rs = [0]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        out.extend((m, k2, r) for r in rs)
    rng.shuffle(out)
    return out


def _bfs_unreached(nb, src, D, N):
    """Number of vertices not within distance D of src, on the adjacency array nb (N x deg)."""
    vis = np.zeros(N, dtype=bool)
    vis[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        mark = np.zeros(N, dtype=bool)
        mark[nb[frontier].ravel()] = True
        mark &= ~vis
        if not mark.any():
            break
        vis |= mark
        frontier = np.flatnonzero(mark)
    return N - int(np.count_nonzero(vis))


def _cost(M, invarr, S, G, D):
    """Unreached pairs from A_1 and B_1 for the Haar graph with connection set S."""
    Sa = np.array(S, dtype=np.int64)
    Si = invarr[Sa]
    N = 2 * G
    nb = np.empty((N, len(S)), dtype=np.int64)
    nb[:G] = G + M[:, Sa]   # A_g ~ B_{g s}
    nb[G:] = M[:, Si]       # B_h ~ A_{h s^{-1}}
    return _bfs_unreached(nb, 0, D, N) + _bfs_unreached(nb, G, D, N)


def _climb(M, invarr, G, d, D, rng, cap, iters):
    """Simulated annealing over S (identity fixed in position 0). Returns S with cost 0, or None."""
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost(M, invarr, S, G, D)
    for it in range(iters):
        if cost == 0:
            return S
        if time.monotonic() > cap:
            break
        temp = 1.0 * (1.0 - it / iters) + 0.05
        pos = rng.randrange(1, d)
        new = rng.randrange(G)
        if new in S:
            continue
        S2 = list(S)
        S2[pos] = new
        c2 = _cost(M, invarr, S2, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            S, cost = S2, c2
    return S if cost == 0 else None


def _try_order(G, d, D, rng, cap):
    """Try several groups of order G; return (n, edges) for a valid Haar graph, or None."""
    cands = _group_candidates(G, rng)
    for (m, k2, r) in cands[:8]:
        if time.monotonic() > cap:
            return None
        M = _semidirect_table(m, k2, r)
        invarr = np.empty(G, dtype=np.int64)
        rows, cols = np.nonzero(M == 0)
        invarr[cols] = rows
        S = _climb(M, invarr, G, d, D, rng, cap, 800)
        if S is not None:
            edges = [(g, G + int(M[g, s])) for g in range(G) for s in S]
            n = 2 * G
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2 (and K_2 for d = 1).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 1 or D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # Haar-graph search over groups, ascending in group order G.
    Gmax = max(d, lib.moore_bound(d, D) // 2)
    G = max(d, best_n // 2 + 1)
    try:
        while G <= Gmax and time.monotonic() < deadline:
            cap = min(deadline, time.monotonic() + 1.5)
            res = _try_order(G, d, D, rng, cap)
            if res is not None:
                consider(res[0], res[1])
            G += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
