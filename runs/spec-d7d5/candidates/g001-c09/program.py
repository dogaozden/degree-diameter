import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction: bi-regular voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: a A-parts and a B-parts (a = 1 or 2). Between A-part i and B-part j
# there are K[i][j] darts, each carrying a group voltage g. The lift has vertex
# (part, x) for x in the group; a dart (i, j, g) joins (A_i, x) to (B_j, x*g).
# Row and column sums of K equal d, so the lift is d-regular and bipartite.
#
# New ideas in this program (not in the parent):
#  * Fiber-transitivity reduction: left multiplication by h is an automorphism
#    of every lift, so distances from (part, identity) to all vertices determine
#    the diameter. Only P = 2a BFS runs are needed instead of one per vertex.
#  * Coverage-driven local search: the objective is the number of (source, target)
#    pairs farther than D apart. Voltages are moved one at a time and accepted when
#    the objective does not increase.
#  * Vectorized Cayley tables for Z_m x| Z_k built with numpy, plus enumeration of
#    all admissible (m, k, r) for a given order N.
# ----------------------------------------------------------------------------


def _semidirect_table(m, k, r):
    """Return (M, inv): Cayley table of Z_m x|_r Z_k (element (a,b) coded a*k+b, identity 0)."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    A = x // k
    B = x % k
    M = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _groups_of_order(N):
    """All (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1 (r = 1 gives Z_m x Z_k)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if m > 1 and math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _uncovered(P, N, darts, M, D):
    """Count (source, target) pairs at distance > D; 0 iff the lift has diameter <= D.

    darts: list of (u, v, g, g_inv) with u an A-part index and v a B-part index.
    Only one source per part is needed, by fiber-transitivity.
    """
    total = 0
    for src in range(P):
        vis = np.zeros((P, N), dtype=bool)
        vis[src, 0] = True
        front = vis.copy()
        for _ in range(D):
            new = np.zeros((P, N), dtype=bool)
            for u, v, g, gi in darts:
                fu = np.flatnonzero(front[u])
                if fu.size:
                    new[v, M[fu, g]] = True
                fv = np.flatnonzero(front[v])
                if fv.size:
                    new[u, M[fv, gi]] = True
            new &= ~vis
            if not new.any():
                break
            vis |= new
            front = new
        total += P * N - int(vis.sum())
    return total


def _search(a, N, pairs, M, inv, D, rng, t_end, max_moves):
    """Coverage-driven local search over voltages. Returns (vol, objective)."""
    P = 2 * a
    vol = [rng.sample(range(N), c) for _, _, c in pairs]

    def darts():
        out = []
        for (i, j, _), gs in zip(pairs, vol):
            for g in gs:
                out.append((i, a + j, g, int(inv[g])))
        return out

    cur = _uncovered(P, N, darts(), M, D)
    for _ in range(max_moves):
        if cur == 0 or time.monotonic() >= t_end:
            break
        t = rng.randrange(len(pairs))
        idx = rng.randrange(len(vol[t]))
        g_new = rng.randrange(N)
        if g_new in vol[t]:
            continue
        old = vol[t][idx]
        vol[t][idx] = g_new
        f = _uncovered(P, N, darts(), M, D)
        if f <= cur or rng.random() < 0.02:
            cur = f
        else:
            vol[t][idx] = old
    return vol, cur


def _edges(a, N, M, pairs, vol):
    """Expand the voltage lift into an explicit (n, edges) pair."""
    edges = []
    for (i, j, _), gs in zip(pairs, vol):
        for g in gs:
            col = M[:, g].tolist()
            for x in range(N):
                edges.append((i * N + x, (a + j) * N + col[x]))
    return 2 * a * N, edges


def _attempt(N, d, D, rng, t_end):
    """Try to find a valid lift of order 2*a*N. Returns (n, edges) or None."""
    if N < d:
        return None
    groups = _groups_of_order(N)
    if not groups:
        return None
    while time.monotonic() < t_end:
        m, k, r = rng.choice(groups)
        M, inv = _semidirect_table(m, k, r)
        if d < 2 or rng.random() < 0.5:
            a = 1
            pairs = [(0, 0, d)]
        else:
            a = 2
            p = rng.randint(1, d - 1)
            pairs = [(i, j, c) for (i, j, c) in
                     [(0, 0, p), (0, 1, d - p), (1, 0, d - p), (1, 1, p)] if c > 0]
        if max(c for _, _, c in pairs) > N:
            continue
        vol, f = _search(a, N, pairs, M, inv, D, rng, t_end, 300)
        if f == 0:
            return _edges(a, N, M, pairs, vol)
    return None


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} for D >= 2, an edge for D = 1."""
    cands = []
    if D >= 2 and d >= 1:
        cands.append(lib.haar_graph(d, range(d)))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, e in cands:
        if lib.is_valid(n, e, d, D):
            return (n, e)
    return (1, [])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Calibration case: the projective plane meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    deadline = start + max(0.5, 0.82 * time_limit - 1.0)
    best = _fallback(d, D)

    # Target case starts near the record group order (record n = 1134 = 2*567).
    N = max(d, 2)
    if d == 7 and D == 5:
        N = 520

    lo, hi, tries = 0, None, {}
    while time.monotonic() < deadline:
        N = max(N, d)
        remaining = deadline - time.monotonic()
        budget = min(max(0.8, remaining / 5.0), 12.0)
        t_end = min(deadline, time.monotonic() + budget)
        res = _attempt(N, d, D, rng, t_end)
        if res is not None:
            n, edges = res
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            lo = N
            if hi is not None and hi <= N:
                hi = None
            if hi is None:
                N = lo + max(1, lo // 60)
            elif hi - lo > 1:
                N = (lo + hi) // 2
            else:
                N = hi
        else:
            tries[N] = tries.get(N, 0) + 1
            if tries[N] >= 2:
                hi = N if hi is None else min(hi, N)
                if hi - lo > 1:
                    N = (lo + hi) // 2
                else:
                    N = hi
    return best
