import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 baseline, the parent's 394 construction)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW: multi-orbit cyclic lifts with translation-reduced diameter check.
#
# Vertices: A-orbit x (x = 0..r-1) holds Z_m copies A_{x,i}; B-orbit y holds B_{y,j}.
# A block S[x][y] is a set of shifts; A_{x,i} ~ B_{y,i+s} for s in S[x][y].
# The block sizes form a circulant pattern with row and column sums d, so the
# graph is d-regular and bipartite, with order 2rm. For r = 1 this is the Haar graph.
#
# Translation by Z_m is an automorphism, so distances from every vertex are
# determined by the 2r representatives A_{x,0} and B_{y,0}. A diameter-3 check is
# then 2r bitset ball computations over m-bit masks, which is far cheaper than
# a full all-pairs BFS. The search anneals the shift values to minimise the number of
# (representative, vertex) pairs at distance more than 3. Any graph found is then
# confirmed with lib.is_valid.
# ----------------------------------------------------------------------------

def _rot(X, s, m, full):
    """Cyclically rotate an m-bit mask so that bit i moves to bit (i + s) mod m."""
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & full


def _ball_uncovered(S, r, m, full, side, idx):
    """Number of vertices NOT within distance 3 of the representative (side, idx, 0)."""
    A = [0] * r
    B = [0] * r
    if side == 0:
        A[idx] = 1
    else:
        B[idx] = 1
    UA = A[:]
    UB = B[:]
    cur = side
    for _ in range(3):
        if cur == 0:
            nB = [0] * r
            for x in range(r):
                X = A[x]
                if X:
                    for y in range(r):
                        acc = nB[y]
                        for s in S[x][y]:
                            acc |= _rot(X, s, m, full)
                        nB[y] = acc
            B = nB
            for y in range(r):
                UB[y] |= B[y]
        else:
            nA = [0] * r
            for y in range(r):
                Y = B[y]
                if Y:
                    for x in range(r):
                        acc = nA[x]
                        for s in S[x][y]:
                            acc |= _rot(Y, (m - s) % m, m, full)
                        nA[x] = acc
            A = nA
            for x in range(r):
                UA[x] |= A[x]
        cur ^= 1
    reached = sum(v.bit_count() for v in UA) + sum(v.bit_count() for v in UB)
    return 2 * r * m - reached


def _lift_uncovered(S, r, m, full):
    """Total uncovered (representative, vertex) pairs over all 2r orbit representatives."""
    total = 0
    for side in (0, 1):
        for idx in range(r):
            total += _ball_uncovered(S, r, m, full, side, idx)
    return total


def _sa_lift(r, m, sizes, deadline, rng):
    """Anneal shift sets so the lift has diameter <= 3. Returns S (r x r lists of shifts) or None."""
    full = (1 << m) - 1
    S = [[rng.sample(range(m), sizes[x][y]) for y in range(r)] for x in range(r)]
    blocks = [(x, y) for x in range(r) for y in range(r)]
    cost = _lift_uncovered(S, r, m, full)
    it = 0
    while cost > 0:
        it += 1
        if (it & 63) == 0 and time.monotonic() > deadline:
            return None
        x, y = blocks[rng.randrange(len(blocks))]
        blk = S[x][y]
        i = rng.randrange(len(blk))
        old = blk[i]
        inblk = set(blk)
        v = rng.randrange(m)
        while v in inblk:
            v = rng.randrange(m)
        blk[i] = v
        new = _lift_uncovered(S, r, m, full)
        delta = new - cost
        T = 1.5 * (0.9997 ** (it % 12000)) + 0.2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            blk[i] = old
    return S


def _lift_graph(r, m, S):
    """Expand the shift sets into an explicit (n, edges) bipartite graph."""
    n = 2 * r * m
    E = []
    for x in range(r):
        for y in range(r):
            for s in S[x][y]:
                for i in range(m):
                    E.append((x * m + i, r * m + y * m + (i + s) % m))
    return n, E


def _lift_search(d, D, best_n, deadline, rng):
    """Round-robin over orbit counts r = 1..4, climbing m while lifts of order > best_n succeed.

    Returns (n, E) for the best valid lift found, or None.
    """
    moore = lib.moore_bound(d, D)
    cur = best_n
    found = None
    rs = [r for r in (1, 2, 3, 4) if r <= d]
    m_next = {r: 1 for r in rs}
    slice_s = {r: 2.0 for r in rs}
    active = list(rs)
    while active and time.monotonic() < deadline:
        for r in list(active):
            now = time.monotonic()
            if now >= deadline:
                break
            m = max(m_next[r], cur // (2 * r) + 1)
            if 2 * r * m > moore:
                active.remove(r)
                continue
            q, rem = divmod(d, r)
            sizes = [[q + (1 if (y - x) % r < rem else 0) for y in range(r)] for x in range(r)]
            if max(max(row) for row in sizes) > m:
                active.remove(r)
                continue
            end = min(deadline, now + slice_s[r])
            S = _sa_lift(r, m, sizes, end, rng)
            if S is None:
                slice_s[r] = min(20.0, slice_s[r] * 1.5)
                m_next[r] = m
                continue
            n, E = _lift_graph(r, m, S)
            if n > cur and lib.is_valid(n, E, d, D):
                cur = n
                found = (n, E)
            m_next[r] = m + 1
    return found


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.7 * float(time_limit), 42.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Baseline: arc-extended projective plane (quick).
        cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        if cands:
            cands.sort(key=lambda t: -t[0])
            n_c, E_c, _side = cands[0]
            consider(n_c, E_c)
        # New: multi-orbit cyclic lifts searched by annealing. Trivially skipped
        # when no lift can beat the current order (e.g., small calibration cases).
        found = _lift_search(d, D, best_n, deadline, rng)
        if found is not None:
            consider(*found)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
