import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. A point set S with every
# line holding <= s points of S and every point on <= s lines of S lets us add
# one A-vertex per point of S (joined to the q+1 lines through it) and one
# B-vertex per element of S (joined to the q+1 points on that line).
# For d=16 (q=13, conic S of 14 points) this gives the record 394.
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return a list of (n, edges) arc-extended graphs, one per usable prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, S, pl, lp))
    return out


# ----------------------------------------------------------------------------
# New construction: cyclic Haar graphs from difference covers (diameter 3).
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, with |S| = k. It is k-regular
# and bipartite on 2m vertices. From a_0:
#   * a-vertices at distance 0 or 2 are {0} and S - S, so S - S = Z_m is needed;
#   * b-vertices at distance 1 or 3 are S and (S - S) + S, and the latter is all
#     of Z_m as soon as S - S = Z_m.
# So any k-subset S of Z_m whose difference set covers Z_m gives diameter 3.
# The bound m <= k^2 - k + 1 (Moore-type) caps the order at 2(k^2 - k + 1).
# We search for difference covers by simulated annealing on the number of
# uncovered residues, sweeping m upward from just above the current best order.
# ----------------------------------------------------------------------------

def _uncovered(S, m):
    """Number of residues mod m not expressible as s - t with s, t in S."""
    seen = bytearray(m)
    for s in S:
        for t in S:
            seen[(s - t) % m] = 1
    return m - sum(seen)


def _cover_search(m, k, rng, end):
    """Anneal a k-set containing 0 in Z_m whose differences cover Z_m; None on timeout."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cost = _uncovered(S, m)
    T = 0.4
    while cost > 0:
        if time.monotonic() > end:
            return None
        i = rng.randrange(1, k)
        v = rng.randrange(1, m)
        if v in S:
            continue
        old = S[i]
        S[i] = v
        c = _uncovered(S, m)
        if c <= cost or rng.random() < math.exp((cost - c) / T):
            cost = c
        else:
            S[i] = old
    return sorted(S)


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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Baseline arc-extended PG graphs (394 for d = 16).
        for n, e in _arc_candidates(d, start + 0.2 * time_limit, rng):
            consider(n, e)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 3:
        # New search: difference-cover Haar graphs, k = d, diameter 3.
        k = d
        if k >= 2:
            mmax = k * (k - 1) + 1
            while time.monotonic() < deadline:
                mlo = max(k, best_n // 2 + 1)
                if mlo > mmax:
                    break
                remaining = deadline - time.monotonic()
                cnt = mmax - mlo + 1
                per = min(3.0, max(1.0, remaining / cnt))
                for m in range(mlo, mmax + 1):
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    S = _cover_search(m, k, rng, min(deadline, now + per))
                    if S is not None:
                        n, e = lib.haar_graph(m, S)
                        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
