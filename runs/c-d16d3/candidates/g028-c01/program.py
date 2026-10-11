import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction 1 (safe baseline, D = 3): arc-extended projective plane incidence.
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d-q-1. Choose a point set S_A and a
# line set S_B so that each line lies in at most s points of S_A and each point
# lies on at most s lines of S_B. Add a new A-vertex joined to the q+1 lines
# through each P in S_A, and a new B-vertex joined to the q+1 points of each
# line in S_B. Distances stay <= 3.
# ----------------------------------------------------------------------------

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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex for each element of S."""
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


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q+1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
    """W(q) for the largest prime power q <= min(d-1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Construction 2 (new, bold, D = 3): Haar graphs from difference covers.
#
# Let G be a finite abelian group of order m and S a subset of size d with 0 in S.
# The Haar graph H(G, S): vertices a_x and b_x (x in G), with a_x ~ b_{x+s} for s in S.
# It is bipartite and d-regular with 2m vertices.
#   * a_x to a_y (distance 2) exists iff y-x is in S-S (distinct s, t).
#   * a_x to b_y (distance <= 3) holds because S-S+S contains (S-S)+s0 = G.
# So if S-S covers all of G, the diameter is at most 3. Order 2m is valid whenever
# the cover exists. The Moore-type limit is m <= d(d-1)+1, i.e. order <= 2(d^2-d+1).
# For d = 16 we need m >= 198 to beat 394.
# The search is simulated annealing over S that minimizes the number of uncovered
# nonzero group elements, with a focused move that targets an uncovered element.
# ----------------------------------------------------------------------------

def _group_tables(m1, m2):
    """Difference table for the abelian group Z_m1 x Z_m2 (element (a,b) coded as a*m2+b)."""
    N = m1 * m2
    A = [x // m2 for x in range(N)]
    B = [x % m2 for x in range(N)]
    DIFF = [[((A[x] - A[y]) % m1) * m2 + (B[x] - B[y]) % m2 for y in range(N)]
            for x in range(N)]
    return N, DIFF


def _swap(S, i, u, counts, unc, DIFF, k):
    """Replace S[i] by u, updating the ordered-difference counts; return the new uncovered count."""
    old = S[i]
    row_o = DIFF[old]
    for j in range(k):
        if j != i:
            t = S[j]
            c = row_o[t]
            counts[c] -= 1
            if counts[c] == 0:
                unc += 1
            c = DIFF[t][old]
            counts[c] -= 1
            if counts[c] == 0:
                unc += 1
    S[i] = u
    row_u = DIFF[u]
    for j in range(k):
        if j != i:
            t = S[j]
            c = row_u[t]
            if counts[c] == 0:
                unc -= 1
            counts[c] += 1
            c = DIFF[t][u]
            if counts[c] == 0:
                unc -= 1
            counts[c] += 1
    return unc


def _anneal_cover(N, DIFF, k, rng, deadline):
    """Find S of size k in a group of order N (0 in S) whose nonzero differences cover the group."""
    if k < 2 or N < k:
        return None
    T0, T1, L = 1.0, 0.08, 30000
    ratio = (T1 / T0) ** (1.0 / L)
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), k - 1)
        counts = [0] * N
        for x in S:
            row = DIFF[x]
            for y in S:
                if x != y:
                    counts[row[y]] += 1
        unc = sum(1 for g in range(1, N) if counts[g] == 0)
        T = T0
        for t in range(L):
            if unc == 0:
                return S
            if (t & 1023) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, k)
            old = S[i]
            if rng.random() < 0.6:
                g = -1
                for _ in range(20):
                    c = rng.randrange(1, N)
                    if counts[c] == 0:
                        g = c
                        break
                if g < 0:
                    g = rng.randrange(1, N)
                u = DIFF[S[rng.randrange(k)]][g]  # s - u = g covers g
            else:
                u = rng.randrange(1, N)
            if u in S:
                T *= ratio
                continue
            old_unc = unc
            unc = _swap(S, i, u, counts, unc, DIFF, k)
            delta = unc - old_unc
            if delta > 0 and rng.random() >= math.exp(-delta / T):
                unc = _swap(S, i, old, counts, unc, DIFF, k)
            T *= ratio
        if unc == 0:
            return S
    return None


def _haar_graph(m1, m2, S):
    """Haar graph of Z_m1 x Z_m2 with connection set S: a_x ~ b_{x+s}. Returns (2N, edges)."""
    N = m1 * m2
    edges = []
    for x in range(N):
        ax, bx = divmod(x, m2)
        for s in S:
            as_, bs = divmod(s, m2)
            y = ((ax + as_) % m1) * m2 + (bx + bs) % m2
            edges.append((x, N + y))
    return 2 * N, edges


def _haar_candidates(lo, hi):
    """Abelian groups of order m in [lo, hi], as (m, m1, m2) with m1 | m2 (m1 = 1 means cyclic)."""
    out = []
    for m in range(lo, hi + 1):
        out.append((m, 1, m))
        m1 = 2
        while m1 * m1 <= m:
            if m % (m1 * m1) == 0:
                out.append((m, m1, m // m1))
            m1 += 1
    return out


def _haar_search(d, lo, hi, deadline, rng, consider, best_n_fn):
    """Anneal difference covers over candidate groups, smallest order first, with growing time slices."""
    cands = _haar_candidates(lo, hi)
    cache = {}
    cap = 0.3
    while time.monotonic() < deadline:
        target = best_n_fn() // 2
        active = [c for c in cands if c[0] > target]
        if not active:
            return
        for m, m1, m2 in active:
            now = time.monotonic()
            if now >= deadline:
                return
            if m <= best_n_fn() // 2:
                continue
            key = (m1, m2)
            if key not in cache:
                cache[key] = _group_tables(m1, m2)
            N, DIFF = cache[key]
            S = _anneal_cover(N, DIFF, d, rng, min(deadline, now + cap))
            if S is not None:
                n_c, e_c = _haar_graph(m1, m2, S)
                consider(n_c, e_c)
        cap *= 2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        b = state["best"]
        if n > b[0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)
            return True
        return False

    if D == 2:
        return state["best"]

    # Baseline: arc-extended projective planes (diameter 3).
    for n, e in _arc_candidates(d, deadline, random.Random(seed * 7919 + d)):
        consider(n, e)

    # Generalized quadrangle (diameter 4), only useful when D >= 4.
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New construction: Haar graphs from difference covers (diameter 3).
    if time.monotonic() < deadline:
        lo = state["best"][0] // 2 + 1
        hi = min(d * (d - 1) + 1, 260, lo + 80)
        if lo <= hi:
            _haar_search(d, lo, hi, deadline, rng, consider, lambda: state["best"][0])

    b = state["best"]
    if not lib.is_valid(b[0], b[1], d, D):
        b = lib.haar_graph(d, range(d))
    return b
