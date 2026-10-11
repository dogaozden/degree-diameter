import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold construction: Haar graphs from difference covers (diameter 3).
#
# For a cyclic group Z_n and a set S of size d, the Haar graph H(n, S) has
# vertices a_i, b_j (i, j in Z_n), with a_i ~ b_{i+s} for s in S. It is
# d-regular and bipartite. If S - S = Z_n then:
#   * two a's (or two b's) share a neighbour, so they are at distance 2;
#   * a_0 to b_j has distance 3 via j in (S - S) + S = Z_n + S = Z_n.
# So the diameter is 3 and the order is 2n. Since n <= 1 + d(d-1), the ceiling
# is 2(d^2 - d + 1), which is 482 for d = 16. Finding a small cover set S with
# |S| = d and S - S = Z_n is a local search problem.
#
# Fallbacks: the arc-extended projective plane graph (diameter 3) and K_{d,d}
# (diameter 2), each checked with lib.is_valid.
# ----------------------------------------------------------------------------


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Old PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _saturate(n, edges, m, k, d, rng):
    """Add missing X-Y edges while both endpoints have spare degree. Keeps bipartite and diameter."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended PG(2, q) for each prime power q <= d - 1."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Difference-cover local search on Z_n.
# cnt[t] = number of ordered pairs (a, b) in S with a - b = t (mod n).
# Cost = number of nonzero t with cnt[t] == 0 (uncovered differences).
# ----------------------------------------------------------------------------

def _move(cnt, S, i, y, n):
    """Replace S[i] by y, update cnt in place, and return the change in uncovered count."""
    x = S[i]
    delta = 0
    for j, z in enumerate(S):
        if j == i:
            continue
        for t in ((x - z) % n, (z - x) % n):
            cnt[t] -= 1
            if cnt[t] == 0:
                delta += 1
    S[i] = y
    for j, z in enumerate(S):
        if j == i:
            continue
        for t in ((y - z) % n, (z - y) % n):
            if cnt[t] == 0:
                delta -= 1
            cnt[t] += 1
    return delta


def _diff_cover(k, n, rng, deadline):
    """Search for a k-subset S of Z_n with S - S = Z_n. Returns sorted S or None."""
    if n < k or n - 1 > k * (k - 1):
        return None
    S = rng.sample(range(n), k)
    cnt = [0] * n
    for i in range(k):
        for j in range(i + 1, k):
            cnt[(S[i] - S[j]) % n] += 1
            cnt[(S[j] - S[i]) % n] += 1
    U = sum(1 for t in range(1, n) if cnt[t] == 0)
    if U == 0:
        return sorted(S)
    T = 0.6
    while True:
        if time.monotonic() > deadline:
            return None
        for _ in range(300):
            i = rng.randrange(k)
            y = rng.randrange(n)
            if y in S:
                continue
            x = S[i]
            delta = _move(cnt, S, i, y, n)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                U += delta
                if U == 0:
                    return sorted(S)
            else:
                _move(cnt, S, i, x, n)


def _cyclic_search(k, deadline, rng, per_n):
    """Climb n upward from k+1; return (n, S) for the largest n found before the first failure."""
    best = None
    n = k + 1
    while n - 1 <= k * (k - 1):
        now = time.monotonic()
        if now > deadline:
            break
        S = _diff_cover(k, n, rng, min(deadline, now + per_n))
        if S is None:
            break
        best = (n, S)
        n += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        # Cheap diameter-3 candidates first (arc-extended projective planes).
        arc_deadline = start + 0.25 * time_limit
        for n_c, e_c in sorted(_arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d)),
                               key=lambda t: -t[0]):
            consider(n_c, e_c)

        # Bold attempt: Haar graph from a difference cover of Z_n with |S| = d.
        total = deadline - start
        per_n = max(0.5, 0.15 * total)
        res = _cyclic_search(d, deadline, rng, per_n)
        if res is not None:
            n, S = res
            hn, he = lib.haar_graph(n, S)
            consider(hn, he)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
