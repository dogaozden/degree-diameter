import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Conic-extended projective plane graphs (diameter 3).
#
# Start from the PG(2, q) incidence graph (degree q+1). With d >= q+2 each
# vertex has spare capacity s = d-q-1. Take S = a conic (plus its nucleus for
# even q), an arc with at most 2 points on any line. Add an A-vertex joined to
# the lines through each P in S, and a B-vertex joined to the points of each
# line j in S. For d = 16, q = 13 this gives 394 vertices.
# ----------------------------------------------------------------------------

def _conic_arc(q, d):
    """Return (n, edges) of the conic-extended PG(2,q) graph, or None if no spare capacity."""
    if d - q - 1 < 1:
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    m2, inc = lib.projective_plane_incidence(q)
    m = m2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in inc:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    E = list(inc)
    k = len(S)
    for t, P in enumerate(S):
        x = 2 * m + t
        E.extend((x, m + L) for L in point_lines[P])
    for t, j in enumerate(S):
        b = 2 * m + k + t
        E.extend((Q, b) for Q in line_points[j])
    return 2 * m + 2 * k, E


# ----------------------------------------------------------------------------
# Difference-cover search for Haar graphs of Z_m (diameter 3).
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d. With 0 in S it is
# bipartite, d-regular, and has diameter <= 3 exactly when S - S = Z_m
# (a-a and b-b distances are 0/2, a-b distances are 1 or 3 since 0 is in S).
# Such S forces m <= d(d-1)+1, and we search for S by simulated annealing
# on the number of covered nonzero differences, using O(d) incremental updates.
# ----------------------------------------------------------------------------

def _diff_search(m, k, rng, end):
    """Find S of size k in Z_m with 0 in S and S - S = Z_m. Return S or None at time `end`."""
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    cov = [sum(1 for x in range(1, m) if cnt[x] > 0)]

    def swap(i, new):
        old = S[i]
        for t in S:
            if t != old:
                for x in ((old - t) % m, (t - old) % m):
                    cnt[x] -= 1
                    if cnt[x] == 0:
                        cov[0] -= 1
        inS[old] = False
        S[i] = new
        inS[new] = True
        for t in S:
            if t != new:
                for x in ((new - t) % m, (t - new) % m):
                    if cnt[x] == 0:
                        cov[0] += 1
                    cnt[x] += 1

    T = 0.7
    it = 0
    while cov[0] < m - 1:
        it += 1
        if (it & 127) == 0 and time.monotonic() > end:
            return None
        i = rng.randrange(1, k)
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        old = S[i]
        before = cov[0]
        swap(i, new)
        delta = cov[0] - before
        if delta >= 0 or rng.random() < math.exp(delta / T):
            T = max(0.05, T * 0.99995)
        else:
            swap(i, old)
    return list(S)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, E):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, E, d, D):
            best = (n, E)
            best_n = n

    if D < 3:
        return best

    # Conic-extended projective plane graphs (diameter 3).
    for q in range(2, d):
        if time.monotonic() > deadline:
            break
        if lib.is_prime_power(q):
            res = _conic_arc(q, d)
            if res is not None:
                consider(res[0], res[1])

    # Bold change: Haar graphs of cyclic groups from a difference-cover search.
    # Start just above the current best order and climb while the search succeeds.
    # Any Haar graph found has diameter <= 3, so it is valid for every D >= 3.
    if d >= 2:
        m = max(d, best_n // 2 + 1)
        m_hi = d * (d - 1) + 1
        while m <= m_hi:
            now = time.monotonic()
            if now >= deadline:
                break
            budget = max(0.5, 0.3 * (deadline - now))
            S = _diff_search(m, d, rng, min(deadline, now + budget))
            if S is None:
                break
            n, E = lib.haar_graph(m, S)
            consider(n, E)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
