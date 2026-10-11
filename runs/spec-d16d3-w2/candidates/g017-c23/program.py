import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (new, primary for D >= 3): bi-Cayley "Haar" graphs over Z_m.
#
# H(m, S) has parts A = {a_i}, B = {b_j}, with a_i ~ b_{i+s} for s in S, |S| = d.
# Same-side pairs a_i, a_j are at distance 2 iff j - i lies in S - S, and
# cross pairs are at distance <= 3 whenever S - S = Z_m (then S - S + S = Z_m).
# So any d-subset S with S - S = Z_m gives a bipartite d-regular graph of
# diameter 3 and order 2m. The Moore-type ceiling is m <= d(d-1)+1, which for
# d = 16 gives 482 vertices. We search for difference covers of size d by
# annealing on the number of uncovered differences, and try m upward.
# ----------------------------------------------------------------------------

def _swap(cnt, m, S, i, new):
    """Replace S[i] by new, updating difference counts cnt; return change in #uncovered residues."""
    old = S[i]
    delta = 0
    others = [S[j] for j in range(len(S)) if j != i]
    for t in others:
        x = (old - t) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            delta += 1
        x = (t - old) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            delta += 1
    for t in others:
        x = (new - t) % m
        if cnt[x] == 0:
            delta -= 1
        cnt[x] += 1
        x = (t - new) % m
        if cnt[x] == 0:
            delta -= 1
        cnt[x] += 1
    S[i] = new
    return delta


def _cover_search(m, k, rng, deadline):
    """Search a k-subset S of Z_m (0 in S) with S - S = Z_m. Returns S or None on timeout."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    T = 0.6
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        delta = _swap(cnt, m, S, i, new)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            unc += delta
        else:
            _swap(cnt, m, S, i, old)
    return S


# ----------------------------------------------------------------------------
# Construction B (safety, from parent): arc-extended projective plane graphs.
# Start from PG(2, q) incidence (degree q+1); spare capacity s = d - q - 1 per
# vertex lets us add a new A-vertex per point of an arc S and a new B-vertex
# per line of S. For d = 16, q = 13, the conic gives 394 vertices.
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


_point_lines_cache = [None]


def _arc_graph(m, edges, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in _point_lines_cache[0][P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return candidates (n, edges, m, point_lines, line_points) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _point_lines_cache[0] = point_lines
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, S, line_points)
        out.append((n_c, e_c, m, point_lines, line_points))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4), from parent.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Safety candidates from the arc-extended projective plane graphs.
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        for c in sorted(cands, key=lambda t: -t[0]):
            consider(c[0], c[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Primary bold search: difference-cover Haar graphs (diameter 3, degree d).
    # Only sizes beating the current best (2m > best_n) matter, so start there
    # and increase m while searches keep succeeding.
    if D >= 3:
        m = max(d, best_n // 2 + 1)
        hi = d * (d - 1) + 1
        while m <= hi and time.monotonic() < deadline:
            now = time.monotonic()
            budget = (deadline - now) * 0.6
            S = _cover_search(m, d, rng, now + budget)
            if S is None:
                break
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
