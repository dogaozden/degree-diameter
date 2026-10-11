import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Haar graphs of cyclic groups as the main family.
#
# Haar graph H(m, S): vertices a_i, b_j (i, j in Z_m), a_i ~ b_{i+s} for s in S.
# It is bipartite and |S|-regular. With 0 in S (WLOG by translation):
#   - same-side distance <= 2 for all pairs iff S - S covers Z_m \ {0};
#   - cross-side distance <= 3 for all pairs iff S - S + S covers Z_m.
# So diameter 3 holds exactly when both covering conditions hold. This is a
# difference-covering problem, not a dense-search problem, and it allows
# m up to about d(d-1)+1 (perfect difference sets) for D = 3.
# ----------------------------------------------------------------------------

def _cover_cost(m, S_arr, eye):
    """Number of uncovered residues (same-side nonzero differences plus cross-side residues). Zero means D = 3."""
    D2 = (S_arr[:, None] - S_arr[None, :]) % m
    same = np.zeros(m, dtype=bool)
    same[D2[eye]] = True
    X = (D2[:, :, None] + S_arr[None, None, :]) % m
    cross = np.zeros(m, dtype=bool)
    cross[X.ravel()] = True
    return (m - 1 - int(same.sum())) + (m - int(cross.sum()))


def _bfs_cost(m, S, D):
    """Generic cost for any D: vertices not within distance D of a_0 or b_0 (Haar graphs are side-transitive)."""
    total = 0
    N = 2 * m
    for src in (0, m):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < m:
                    for s in S:
                        v = m + (u + s) % m
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j = u - m
                    for s in S:
                        v = (j - s) % m
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _search(m, d, cost, rng, deadline):
    """Hill-climb a connection set S of size d containing 0 in Z_m with cost zero, with restarts."""
    if d < 2 or m < d:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        c = cost(S)
        stall = 0
        while c > 0 and stall < 2000:
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            new = rng.randrange(1, m)
            if new in S:
                stall += 1
                continue
            T = S[:]
            T[i] = new
            ct = cost(T)
            if ct < c:
                S, c = T, ct
                stall = 0
            elif ct == c or rng.random() < 0.01:
                S, c = T, ct
                stall += 1
            else:
                stall += 1
        if c == 0:
            return S
    return None


# ----------------------------------------------------------------------------
# Projective plane fallback (diameter 3).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (capped for speed)."""
    for q in range(min(d - 1, 60), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = [2 * d, lib.haar_graph(d, range(d))[1]]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D == 2 or d < 2:
        n, e = lib.haar_graph(d, range(d))
        return n, e

    rng = random.Random(seed)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    hi = d * (d - 1) + 1 if D == 3 else lib.moore_bound(d, D) // 2

    if D == 3:
        # Feasibility is not monotone in m (e.g. Z_7 works, Z_6 does not),
        # so scan upward from the smallest m that could beat the current best.
        eye = ~np.eye(d, dtype=bool)
        lo_t = max(d, best[0] // 2)
        for m in range(lo_t, hi + 1):
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            budget = min(remaining, 2.0 * remaining / max(1, hi - m + 1))

            def cost(S, m=m):
                return _cover_cost(m, np.array(S, dtype=np.int64), eye)

            S = _search(m, d, cost, rng, now + budget)
            if S:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
    else:
        # Larger D: binary search on m with the generic BFS cost (heuristic).
        lo = d - 1
        while lo < hi and time.monotonic() < deadline:
            mid = (lo + hi + 1) // 2
            now = time.monotonic()
            budget = max(0.5, 0.3 * (deadline - now))
            end = min(deadline, now + budget)

            def cost(S, m=mid):
                return _bfs_cost(m, S, D)

            S = _search(mid, d, cost, rng, end)
            if S is not None:
                n, e = lib.haar_graph(mid, S)
                if lib.is_valid(n, e, d, D):
                    consider(n, e)
                    lo = mid
                    continue
            hi = mid - 1

    n, e = best[0], best[1]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
