import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Dual-family extension of PG(2, q) incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Every old vertex has degree q+1, so spare s = d-q-1 per vertex.
#
# Add k "X" vertices, each joined to a set N_i of lines, and k "Y" vertices,
# each joined to a set T_i of points. The same vector family F = {N_i} (indexed
# by the common vector list of PG(2, q)) is used for both. A family is valid iff
#   (a) covering: every vector x has some j in N_i with x.j = 0 (so X_i reaches
#       every point within 2, and Y_i reaches every line within 2 by duality),
#   (b) pairwise intersecting: N_i and N_j share an index (distance <= 2 between
#       two X's or two Y's),
#   (c) capacity: every index is used by at most s sets (old degree stays <= d),
#   (d) every set has size <= d.
# Cross distances X_i to Y_j are then <= 3 automatically, so the order is
# 2(q^2+q+1) + 2k. The star family at an arc (conic, or hyperoval for even q)
# gives k = q+1 (order 394 for d=16). This program searches, by simulated
# annealing on the swap-cost, for families with k = q+2, q+3, ... that beat it.
# ----------------------------------------------------------------------------


def _incidence(q):
    """Return (m, M, edges): M[x, y] = 1 iff point x lies on line y (same vector list)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    M = np.zeros((m, m), dtype=np.int32)
    for u, v in edges:
        M[u, v - m] = 1
    return m, M, edges


def _family_cost(M, fam, m, s):
    """Number of violations of (a) covering, (b) intersection, (c) capacity."""
    if not fam:
        return 0
    k = len(fam)
    B = np.zeros((k, m), dtype=np.int32)
    for i, S in enumerate(fam):
        B[i, S] = 1
    cov = B @ M
    inter = B @ B.T
    u = B.sum(axis=0)
    return int((cov == 0).sum()) + int((inter == 0).sum()) // 2 + int(np.maximum(u - s, 0).sum())


def _star_baseline(q, m, NB, s, c, rng):
    """Stars at an arc (conic, plus nucleus or hyperoval point for even q), padded to size c."""
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        conic.append(index[(0, 1, 0)])
    usage = np.zeros(m, dtype=np.int64)
    stars = [list(NB[P]) for P in conic]
    for S in stars:
        usage[S] += 1
    if usage.max() > s:
        stars = [list(NB[conic[0]])]
        usage = np.zeros(m, dtype=np.int64)
        usage[stars[0]] += 1
    for idx, S in enumerate(stars):
        inS = set(S)
        order = [x for x in range(m) if usage[x] < s and x not in inS]
        rng.shuffle(order)
        for x in order:
            if len(S) >= c:
                break
            S.append(x)
            usage[x] += 1
        stars[idx] = S
    return stars


def _sa(M, NB, m, s, fam, deadline, rng, iters):
    """Simulated annealing that repairs a family to zero cost. Returns the family or None."""
    k = len(fam)
    B = np.zeros((k, m), dtype=np.int32)
    mem = []
    for i, S in enumerate(fam):
        B[i, S] = 1
        mem.append(list(S))
    cov = B @ M
    inter = B @ B.T
    u = B.sum(axis=0).astype(np.int32)
    unc = (cov == 0).sum(axis=1).astype(np.int64)
    cost = int(unc.sum()) + int((inter == 0).sum()) // 2 + int(np.maximum(u - s, 0).sum())

    T0, T1 = 1.0, 0.08
    for it in range(iters):
        if cost == 0:
            break
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(k)
        Mi = mem[i]
        a = Mi[rng.randrange(len(Mi))]
        if unc[i] > 0 and rng.random() < 0.6:
            # Guided move: bring in a line through a point that set i does not yet cover.
            pts_unc = np.flatnonzero(cov[i] == 0)
            x = int(pts_unc[rng.randrange(len(pts_unc))])
            b = NB[x][rng.randrange(len(NB[x]))]
        else:
            b = rng.randrange(m)
        if B[i, b]:
            continue

        newcov = cov[i] - M[a] + M[b]
        unc_new = int(np.count_nonzero(newcov == 0))
        dvec = B[:, b] - B[:, a]
        dvec[i] = 0
        z_old = int(np.count_nonzero(inter[i] == 0))
        z_new = int(np.count_nonzero(inter[i] + dvec == 0))
        ua = int(u[a])
        ub = int(u[b])
        dcap = (max(ua - 1 - s, 0) - max(ua - s, 0)) + (max(ub + 1 - s, 0) - max(ub - s, 0))
        delta = (unc_new - int(unc[i])) + (z_new - z_old) + dcap

        if delta <= 0 or rng.random() < math.exp(-delta / T):
            B[i, a] = 0
            B[i, b] = 1
            cov[i] = newcov
            inter[i] += dvec
            inter[:, i] += dvec
            u[a] -= 1
            u[b] += 1
            unc[i] = unc_new
            Mi[Mi.index(a)] = b
            cost += delta

    return mem if cost == 0 else None


def _extend(M, NB, m, s, c, base, deadline, rng):
    """Find a valid family with one more set than base, by restarted annealing."""
    while time.monotonic() < deadline:
        fam = [list(S) for S in base]
        fam.append(rng.sample(range(m), min(c, m)))
        res = _sa(M, NB, m, s, fam, deadline, rng, iters=150000)
        if res is not None:
            return res
    return None


def _family_for_q(q, d, deadline, rng):
    """Return (family, m, edges) for PG(2, q) with spare s = d-q-1."""
    m, M, edges = _incidence(q)
    s = d - q - 1
    if s <= 0:
        return [], m, edges
    c = min(d, m)
    NB = [np.flatnonzero(M[x]).tolist() for x in range(m)]
    # Counting bound: each set meets k-1 others through elements shared with at most s-1 others.
    kmax = min(1 + d * (s - 1), (s * m) // (q + 1))

    fam = _star_baseline(q, m, NB, s, c, rng)
    if _family_cost(M, fam, m, s) != 0:
        fam = [list(NB[0])]
    while len(fam) < kmax and time.monotonic() < deadline:
        res = _extend(M, NB, m, s, c, fam, deadline, rng)
        if res is None:
            break
        fam = res
    return fam, m, edges


def _graph(m, edges, fam):
    """Assemble the graph: PG incidence plus X_i (on lines of N_i) and Y_i (on points of N_i)."""
    k = len(fam)
    base = 2 * m
    E = [(int(u), int(v)) for u, v in edges]
    for i, S in enumerate(fam):
        x = base + i
        for L in S:
            E.append((m + int(L), x))
        y = base + k + i
        for p in S:
            E.append((int(p), y))
    return base + 2 * k, E


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
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Diameter-3 families. Order each candidate by its counting upper bound.
    cands = []
    for q in range(2, d):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        m = q * q + q + 1
        kmax = 0 if s == 0 else min(1 + d * (s - 1), (s * m) // (q + 1))
        cands.append((2 * (m + kmax), q))
    cands.sort(reverse=True)

    for ub, q in cands:
        if ub <= best_n or time.monotonic() >= deadline:
            continue
        fam, m, edges = _family_for_q(q, d, deadline, rng)
        n, E = _graph(m, edges, fam)
        consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
