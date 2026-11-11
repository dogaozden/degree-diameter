"""Random bipartite regular graphs for the d=10, D=5 target (numpy + lib only).

NEW IDEA.  Instead of Haar graphs over groups, take N A-vertices and N B-vertices and join them by d = 10
random perfect matchings (union of 10 random permutations, duplicate edges dropped).  Every vertex has degree
at most d, and the graph is bipartite by construction.  Heuristically, a random 10-regular bipartite graph on
2N vertices has diameter 5 w.h.p. once N is around (d-1)^D / (2 ln N), roughly 3000 to 4000 per side.  Each
candidate is verified exactly with lib.is_valid.  A binary search on N keeps the largest size that passes.

SAFETY.  Only a graph that passes lib.is_valid is returned.  If no random candidate passes in time, the
previous valid Haar graph (order 3582) is returned, and if that fails, the small trivial graph.
"""
import time

import numpy as np

import lib


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def random_bip_graph(N, d, rng):
    """Bipartite graph with parts A = 0..N-1, B = N..2N-1, the union of d random perfect matchings.
    Duplicate edges are merged, so every degree is at most d."""
    idx = np.arange(N, dtype=np.int64)
    parts = []
    for _ in range(d):
        p = rng.permutation(N).astype(np.int64)
        parts.append(idx * N + p)
    codes = np.unique(np.concatenate(parts))
    a = codes // N
    b = codes % N + N
    return 2 * N, list(zip(a.tolist(), b.tolist()))


def haar_fallback():
    """The earlier valid Haar graph over Z_199 x| Z_9 (order 1791, 3582 vertices), with its connection set."""
    m, k, lam = 199, 9, 180
    S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
    N = m * k
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    edges = []
    for s in S:
        a_s, j_s = divmod(s, k)
        t = ((a_s + pw[j_s] * a) % m) * k + (j_s + j) % k
        edges.extend(zip(g.tolist(), (N + t).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != (10, 5):
        return trivial(d, D)
    try:
        t0 = time.monotonic()
        budget = max(1.0, min(0.7 * time_limit, time_limit - 6.0))
        deadline = t0 + budget
        rng = np.random.default_rng(seed)

        best = None
        lo, hi = 1800, 4400          # per-side sizes N; lo is assumed feasible, hi infeasible
        while hi - lo > 20 and time.monotonic() < deadline:
            mid = (lo + hi) // 2
            ok = False
            for _ in range(3):
                if time.monotonic() >= deadline:
                    break
                n, edges = random_bip_graph(mid, d, rng)
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    ok = True
                    break
            if ok:
                lo = mid
            else:
                hi = mid
        if best is not None:
            return best
    except Exception:
        pass

    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
