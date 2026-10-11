import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (order N, base shape) within one attempt
ITERS = 1500                  # annealing steps per (group, base multiplicity) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search only N in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.8            # seconds per (N) attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley search (new construction).
#
# Group G = Z_m x|_r Z_k of order N acts by left multiplication. The graph has
# b "A-orbits" and b "B-orbits", giving 2*b*N vertices. A base multigraph
# with multiplicity matrix M (row and column sums d) is lifted: each dart
# (i, j, g) joins A_{i,x} to B_{j,x*g} for all x in G. Left multiplication is an
# automorphism, so the diameter is decided by BFS from the identity of each
# of the 2b orbits. b = 1 is the classic bi-Cayley case; b = 2 gives twice as
# many vertices for the same group order, with a richer base graph.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_darts(M, b, N, rng):
    """Darts [i, j, g]: for each base pair (i, j), M[i][j] distinct group elements."""
    darts = []
    for i in range(b):
        for j in range(b):
            for g in rng.sample(range(N), M[i][j]):
                darts.append([i, j, g])
    return darts


def _cost_multi(N, b, T, invs, darts, D):
    """Total count of (source, vertex) pairs NOT within distance D, over the 2b orbit identities."""
    outA = [[] for _ in range(b)]
    inB = [[] for _ in range(b)]
    for i, j, g in darts:
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    off = b * N
    V = 2 * b * N
    sources = [i * N for i in range(b)] + [off + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < off:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = off + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - off, N)
                    row = T[y]
                    for i, h in inB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal_multi(N, b, T, invs, darts, d, D, rng, iters, deadline):
    """Anneal the group labels on darts (per-pair distinct) to zero unreached pairs.

    Mutates darts in place. Returns True if a diameter-D lift was found.
    """
    cur = _cost_multi(N, b, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(len(darts))
        i, j, old = darts[t]
        used = {dd[2] for dd in darts if dd[0] == i and dd[1] == j}
        c = rng.randrange(N)
        if c in used:
            continue
        darts[t][2] = c
        v = _cost_multi(N, b, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[t][2] = old
    return cur == 0


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N and base shapes until a diameter-D lift is found or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    if b == 1:
        shapes = [[[d]]]
    else:
        avals = list(range(1, d))
        rng.shuffle(avals)
        shapes = [[[a, d - a], [d - a, a]] for a in avals[:2]]
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        for M in shapes:
            darts = _random_darts(M, b, N, rng)
            if _anneal_multi(N, b, T, invs, darts, d, D, rng, ITERS, deadline):
                return T, darts
            if time.monotonic() > deadline:
                return None
    return None


def _lift_edges(b, N, T, darts):
    """Edges of the lift: A_{i,x} = i*N + x, B_{j,y} = b*N + j*N + y."""
    off = b * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, off + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    def run(b, end):
        """Descending-window search over group orders N for b-orbit lifts, until end."""
        nonlocal best_n
        Nmax = lib._moore_bound(d, D) // (2 * b)
        top = Nmax if b == 2 else min(Nmax, Nmax // 2 + 6)
        if top < d + 1:
            return
        floor = max(d + 1, int(WINDOW_FRAC * top))
        bestN = best_n // (2 * b)
        budget = BUDGET_START
        while time.monotonic() < end:
            lo = max(floor, bestN + 1)
            if lo > top:
                break
            cands = list(range(lo, top + 1))
            rng.shuffle(cands)
            success = False
            for N in cands:
                now = time.monotonic()
                if now >= end:
                    break
                att_deadline = min(end, now + budget)
                res = _attempt(b, N, d, D, rng, att_deadline)
                if res is None:
                    continue
                T, darts = res
                consider(2 * b * N, _lift_edges(b, N, T, darts))
                bestN = max(bestN, N)
                success = True
                break
            if not success:
                if budget < BUDGET_CAP:
                    budget = min(BUDGET_CAP, budget * 1.5)
                elif floor > d + 1:
                    floor -= 1

    # Phase 1: two-orbit lifts (new construction) get most of the budget.
    # Phase 2: classic single-orbit bi-Cayley search as a fallback with the rest.
    mid = start + 0.6 * (deadline - start)
    run(2, mid)
    run(1, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
