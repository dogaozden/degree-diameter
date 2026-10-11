import itertools
import math
import random
import time

import lib

ANNEAL_ITERS = 4000
KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D >= 3) and W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q capped at 16)."""
    for q in range(min(d - 1, 16), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base cyclic lifts with bitmask reachability.
#
# Base: k A-vertices and k B-vertices. Layer L is a permutation p_L of range(k),
# giving darts (i, p_L[i], a) with voltage a in Z_N. Lifted vertices A_{i,x} and
# B_{j,y} are joined when y = x + a. Each base vertex has degree d, so the lift
# has max degree d and 2kN vertices, all bipartite.
#
# Reachable sets are N-bit integers. Shifting a set by a is a cyclic rotation.
# Translation by Z_N is an automorphism, so sources at x = 0 are enough.
# ----------------------------------------------------------------------------

def _rot(x, a, N, full):
    """Cyclic rotation of an N-bit set: bit x -> bit (x + a) mod N."""
    if a == 0:
        return x
    return ((x << a) | (x >> (N - a))) & full


def _lift_cost(k, N, D, darts):
    """Number of (source, vertex) pairs not within distance D, over all 2k sources at x = 0."""
    full = (1 << N) - 1
    adjA = [[] for _ in range(k)]
    adjB = [[] for _ in range(k)]
    for i, j, a in darts:
        adjA[i].append((j, a))
        adjB[j].append((i, (N - a) % N))
    tot = 2 * k * N
    unreached = 0
    for side in (0, 1):
        for s in range(k):
            visA = [0] * k
            visB = [0] * k
            fA = [0] * k
            fB = [0] * k
            if side == 0:
                fA[s] = visA[s] = 1
            else:
                fB[s] = visB[s] = 1
            for _ in range(D):
                any_new = False
                nB = [0] * k
                for i in range(k):
                    f = fA[i]
                    if f:
                        for j, a in adjA[i]:
                            nB[j] |= _rot(f, a, N, full)
                for j in range(k):
                    x = nB[j] & ~visB[j]
                    nB[j] = x
                    if x:
                        visB[j] |= x
                        any_new = True
                fB = nB
                nA = [0] * k
                for j in range(k):
                    f = fB[j]
                    if f:
                        for i, b in adjB[j]:
                            nA[i] |= _rot(f, b, N, full)
                for i in range(k):
                    x = nA[i] & ~visA[i]
                    nA[i] = x
                    if x:
                        visA[i] |= x
                        any_new = True
                fA = nA
                if not any_new:
                    break
            cnt = sum(v.bit_count() for v in visA) + sum(v.bit_count() for v in visB)
            unreached += tot - cnt
    return unreached


def _anneal(d, D, k, N, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns darts with zero cost, else None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(N)])
    cost = _lift_cost(k, N, D, darts)
    T0 = max(1.0, 0.02 * cost)
    for step in range(iters):
        if cost == 0:
            break
        if (step & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.05
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(N)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _lift_cost(k, N, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            a1, a2 = L * k + i1, L * k + i2
            darts[a1][1], darts[a2][1] = darts[a2][1], darts[a1][1]
            c2 = _lift_cost(k, N, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[a1][1], darts[a2][1] = darts[a2][1], darts[a1][1]
    return darts if cost == 0 else None


def _lift_edges(k, N, darts):
    """Expand darts into the lifted graph: (2kN, sorted edge list)."""
    E = set()
    for i, j, a in darts:
        for x in range(N):
            E.add((i * N + x, (k + j) * N + (x + a) % N))
    return 2 * k * N, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, list(e0))
    if D == 2:
        return best

    if d == 2:
        # Even cycle of length 2D: max degree 2, diameter D, Moore-optimal.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: multi-base cyclic lifts above the current best order.
    tried = 0
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        feas = [k for k in KS if n_best // (2 * k) + 1 <= moore // (2 * k)]
        if not feas:
            break
        k = feas[tried % len(feas)]
        tried += 1
        lo = n_best // (2 * k) + 1
        hi = moore // (2 * k)
        N = max(2, lo + rng.randrange(min(4, hi - lo + 1)))
        darts = _anneal(d, D, k, N, rng, deadline, ANNEAL_ITERS)
        if darts is not None:
            n, e = _lift_edges(k, N, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        n1, e1 = lib.haar_graph(d, range(d))
        best = (n1, list(e1))
    return best
