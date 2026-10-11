import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 construction: PG(2,q) incidence plus a family of "cover" vertices.
#
# Let q be the largest prime power with q+1 <= d, and s = d-q-1 the spare degree.
# A family F of line sets T (each |T| <= d) is admissible when
#   (i)   every point lies on some line of T            (T covers all points),
#   (ii)  any two sets of F share a line,                (pairwise intersecting),
#   (iii) every line lies in at most s sets of F.
# Each T gives an A-vertex joined to the lines of T, and a B-vertex joined to the
# points with the same indices as the lines of T. Incidence is symmetric under
# index swap (point i on line j iff dot(i,j)=0), so the B-side is the same family.
# Under (i)-(iii) every pair of vertices is within distance 3, and the order is
# 2(q^2+q+1) + 2|F|. Pencils through the 14 points of a conic give |F| = 14 (order 394).
#
# New in this version: F is searched by an iterated local search. Each step removes
# one or two sets and re-inserts sets with a weighted greedy cover (_greedy_cover),
# where uncovered points and the existing sets are the elements to hit. Weights of
# elements that stay uncovered grow, so hard constraints get priority. A forced
# prefix of lines through a random point adds diversity.
# ----------------------------------------------------------------------------


def _pg_tables(q):
    """Return (m, pl, lp): pl[p] = lines through point p, lp[L] = points on line L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, pl, lp


def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(min(d - 1, 64), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _index(m, fam):
    """Return (mult, memb): mult[c] = number of sets containing line c, memb[c] = their indices."""
    mult = [0] * m
    memb = [[] for _ in range(m)]
    for i, T in enumerate(fam):
        for c in T:
            mult[c] += 1
            memb[c].append(i)
    return mult, memb


def _greedy_cover(m, pl, lp, sp, d, fam, memb, mult, rng, forced):
    """Weighted greedy search for a new admissible line set T (|T| <= d, or None).

    Elements to hit: the m points (each must lie on a line of T) and one element per
    existing family set (T must share a line with it). A line c covers the points of
    lp[c] and the family sets in memb[c]. Lines are usable while mult[c] < sp[c].
    """
    k = len(fam)
    N = m + k
    w = [1] * N
    order = list(range(m))
    for _ in range(4):
        rng.shuffle(order)
        score = [0] * m
        for c in range(m):
            if mult[c] < sp[c]:
                s = 0
                for e in lp[c]:
                    s += w[e]
                for i in memb[c]:
                    s += w[m + i]
                score[c] = s
        cov = [False] * N
        chosen = [False] * m
        T = []
        left = N

        def cover(e):
            nonlocal left
            cov[e] = True
            left -= 1
            we = w[e]
            for c2 in (pl[e] if e < m else fam[e - m]):
                score[c2] -= we

        def pick(c):
            chosen[c] = True
            T.append(c)
            for e in lp[c]:
                if not cov[e]:
                    cover(e)
            for i in memb[c]:
                if not cov[m + i]:
                    cover(m + i)

        for c in forced:
            if len(T) < d and not chosen[c] and mult[c] < sp[c]:
                pick(c)
        while left > 0 and len(T) < d:
            bc, bs = -1, 0
            for c in order:
                if score[c] > bs and not chosen[c] and mult[c] < sp[c]:
                    bs = score[c]
                    bc = c
            if bc < 0:
                break
            pick(bc)
        if left == 0:
            return T
        for e in range(N):
            if not cov[e]:
                w[e] += 1
    return None


def _forced(m, pl, sp, mult, rng):
    """Optionally force a few usable lines through a random point to diversify the greedy."""
    if rng.random() < 0.5:
        return []
    P = rng.randrange(m)
    cands = [c for c in pl[P] if mult[c] < sp[c]]
    rng.shuffle(cands)
    return cands[:rng.randint(1, 4)]


def _ils(m, pl, lp, sp, d, seed_fam, deadline, rng):
    """Iterated local search over admissible families; returns the largest family found."""
    fam = [list(T) for T in seed_fam]
    best = [list(T) for T in fam]
    while time.monotonic() < deadline:
        saved = [list(T) for T in fam]
        r = 1 if rng.random() < 0.6 else 2
        for _ in range(min(r, len(fam))):
            fam.pop(rng.randrange(len(fam)))
        mult, memb = _index(m, fam)
        fails = 0
        while fails < 4 and time.monotonic() < deadline:
            T = _greedy_cover(m, pl, lp, sp, d, fam, memb, mult, rng,
                              _forced(m, pl, sp, mult, rng))
            if T is None:
                fails += 1
                continue
            fam.append(T)
            for c in T:
                mult[c] += 1
                memb[c].append(len(fam) - 1)
            fails = 0
        if len(fam) > len(best):
            best = [list(T) for T in fam]
        if len(fam) < len(saved):
            fam = saved
    return best


def _conic_seed(q, m, pl, sp):
    """Pencils through the points of a conic (plus nucleus for even q); [] if capacities fail."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    fam = [list(pl[P]) for P in S]
    mult, _ = _index(m, fam)
    if any(mult[c] > sp[c] for c in range(m)):
        return []
    return fam


def _assemble(m, lp, fam):
    """Build (n, edges): PG incidence, A-vertices on the line side of each set, B-vertices on points."""
    f = len(fam)
    n = 2 * m + 2 * f
    E = []
    for L in range(m):
        for P in lp[L]:
            E.append((P, m + L))
    for t, T in enumerate(fam):
        a = 2 * m + t
        b = 2 * m + f + t
        for L in T:
            E.append((a, m + L))
            E.append((b, L))
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4).
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
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)
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
        q = _largest_pg_q(d)
        if q is not None:
            m, pl, lp = _pg_tables(q)
            sp = [d - len(lp[c]) for c in range(m)]
            consider(*_assemble(m, lp, []))
            if d - (q + 1) >= 1 and D == 3:
                seed_fam = _conic_seed(q, m, pl, sp) if q >= 3 else []
                fam = _ils(m, pl, lp, sp, d, seed_fam, deadline, rng)
                consider(*_assemble(m, lp, fam))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
