import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Main construction: bipartite Haar graphs over cyclic groups (diameter 3).
#
# H(n, S) has parts A = {a_x} and B = {b_y}, x, y in Z_n, with a_x ~ b_{x+s}
# for s in S, |S| = d. Vertices have degree d. Two A-vertices a_x, a_y are at
# distance 2 exactly when y - x is a difference s - s' with s, s' in S, so if
# the differences of S cover Z_n \ {0} then same-part distances are at most 2.
# Any cross pair is then at distance at most 3, because every y is
# s1 - s2 + s3 for some s1, s2, s3 in S. So diameter 3 follows from covering
# alone. The order is 2n. Moore bound gives n <= d(d-1)+1 (= 241 for d = 16),
# and the search below looks for covers with n above the record 197.
#
# Covers are found by simulated annealing on S (with 0 fixed in S, WLOG),
# minimizing the number of uncovered nonzero residues.
#
# Safe fallback: the PG(2,q)-based arc-extended incidence graph (diameter 3),
# and K_{d,d} (diameter 2) for D = 2.
# ----------------------------------------------------------------------------


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus a new A-vertex per point of S (joined to its q+1 lines)
    and a new B-vertex per line of S (joined to its q+1 points)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidate(d, deadline, rng):
    """Best arc-extended PG(2,q) graph over prime powers q with q + 1 <= d, or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        if best is None or n_c > best[0]:
            best = (n_c, e_c)
    return best


def _move(S, i, u, cnt, n):
    """Replace S[i] by u, updating the difference counts cnt; return the change in the
    number of uncovered nonzero residues."""
    x = S[i]
    k = len(S)
    dunc = 0
    for j in range(k):
        if j == i:
            continue
        s = S[j]
        a = (x - s) % n
        cnt[a] -= 1
        if cnt[a] == 0:
            dunc += 1
        b = (s - x) % n
        cnt[b] -= 1
        if cnt[b] == 0:
            dunc += 1
    for j in range(k):
        if j == i:
            continue
        s = S[j]
        a = (u - s) % n
        if cnt[a] == 0:
            dunc -= 1
        cnt[a] += 1
        b = (s - u) % n
        if cnt[b] == 0:
            dunc -= 1
        cnt[b] += 1
    S[i] = u
    return dunc


def _find_cover(n, k, rng, deadline, budget):
    """Find a k-subset S of Z_n containing 0 whose differences cover Z_n \\ {0}.
    Simulated annealing; returns sorted S or None."""
    if k > n:
        return None
    S = [0]
    if k > 1:
        S += rng.sample(range(1, n), k - 1)
    inS = [False] * n
    for s in S:
        inS[s] = True
    cnt = [0] * n
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % n] += 1
    unc = sum(1 for z in range(1, n) if cnt[z] == 0)
    if unc == 0:
        return sorted(S)
    if k == 1:
        return None

    t0 = time.monotonic()
    stop = min(deadline, t0 + budget)
    if stop <= t0:
        return None
    T = 0.8
    it = 0
    while True:
        it += 1
        if unc == 0:
            return sorted(S)
        if it & 255 == 0:
            now = time.monotonic()
            if now > stop:
                return None
            frac = min(1.0, (now - t0) / (stop - t0))
            T = 0.8 * (0.12 / 0.8) ** frac
        i = rng.randrange(1, k)
        u = rng.randrange(n)
        if inS[u]:
            continue
        x = S[i]
        dunc = _move(S, i, u, cnt, n)
        if dunc <= 0 or rng.random() < math.exp(-dunc / T):
            unc += dunc
            inS[x] = False
            inS[u] = True
        else:
            _move(S, i, x, cnt, n)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    deadline = start + max(0.5, min(0.75 * tl, tl - 4.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 1000003 + d * 131 + D)

    # Safe fallback: K_{d,d} has diameter 2.
    best = (2 * d, lib.haar_graph(d, range(d))[1])
    best_n = 2 * d

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Fallback: arc-extended projective plane incidence graph (diameter 3).
        arc = _arc_candidate(d, start + 0.2 * tl, random.Random(seed * 7919 + d))
        if arc is not None:
            consider(arc[0], arc[1])

        # Main search: cyclic Haar graphs with S-S covering Z_n \ {0}.
        hi = d * (d - 1) + 1
        n = max(d, int(0.8 * hi))
        fails = 0
        while n <= hi and time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            budget = max(0.5, min(6.0, 0.2 * remaining))
            S = _find_cover(n, d, rng, deadline, budget)
            if S is None:
                fails += 1
                if fails >= 4:
                    break
            else:
                fails = 0
                if 2 * n > best_n:
                    consider(2 * n, lib.haar_graph(n, S)[1])
            n += 1

    if not lib.is_valid(best_n, best[1], d, D):
        return 2 * d, lib.haar_graph(d, range(d))[1]
    return best_n, best[1]
