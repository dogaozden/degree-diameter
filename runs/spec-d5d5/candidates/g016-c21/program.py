import itertools
import math
import random
import time

import lib

ITERS = 3000                  # annealing steps per (candidate, group) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
GROUPS_PER_TRY = 10           # groups tried per candidate within one attempt
MAX_B = 4                     # max base vertices per side in multi-orbit lifts
WINDOW = 60                   # how far above the start order to search


# ----------------------------------------------------------------------------
# Baseline families (cheap, always verified by lib.is_valid before use).
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
# NEW HELPER: multi-orbit group lifts with degree-preserving search.
#
# Base: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, each side with
# degree d. Group G (order N, semidirect product Z_m x| Z_k) acts on each orbit.
# Each "dart" (i, j, g) joins A_i,x to B_j,(x*g) for all x in G. Every A-vertex
# has exactly d darts leaving it and every B-vertex exactly d darts entering it,
# so the lift is d-regular, bipartite, with 2*b*N vertices.
#
# Left multiplication by G is an automorphism, so eccentricities only need to
# be checked from the 2b representatives A_i,1 and B_j,1.
#
# The search state is the list of darts. Moves are (a) change one voltage g, or
# (b) swap the B-endpoints of two darts, which keeps all degrees fixed. Cost is
# the number of (representative, vertex) pairs at distance > D. Simulated
# annealing drives the cost to 0. b = 1 reproduces the single-orbit bi-Cayley
# search, and b > 1 gives orders 2bN that single orbits do not reach.
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


def _init_darts(b, d, N, rng):
    """Random degree-d-regular dart pattern with distinct (i, j, g) triples."""
    A = [i for i in range(b) for _ in range(d)]
    B = A[:]
    rng.shuffle(B)
    darts = [[i, j, rng.randrange(N)] for i, j in zip(A, B)]
    seen = set()
    for dt in darts:
        while tuple(dt) in seen:
            dt[2] = rng.randrange(N)
        seen.add(tuple(dt))
    return darts


def _unreached(b, N, T, invs, darts, D):
    """Count (representative, vertex) pairs at distance > D, over the 2b orbit representatives."""
    M = b * N
    nv = 2 * M
    out = [[] for _ in range(b)]
    inn = [[] for _ in range(b)]
    for i, j, g in darts:
        out[i].append((j, g))
        inn[j].append((i, invs[g]))
    total = 0
    sources = [i * N for i in range(b)] + [M + j * N for j in range(b)]
    for src in sources:
        seen = bytearray(nv)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < M:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = M + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - M, N)
                    row = T[y]
                    for i, gi in inn[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += nv - count
    return total


def _anneal(b, N, T, invs, d, D, rng, iters, deadline):
    """Anneal over dart voltages and B-endpoint swaps; return darts with zero cost, or None."""
    darts = _init_darts(b, d, N, rng)
    cur = _unreached(b, N, T, invs, darts, D)
    nd = len(darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        new = [row[:] for row in darts]
        k = rng.randrange(nd)
        if b == 1 or rng.random() < 0.5:
            new[k][2] = rng.randrange(N)
        else:
            l = rng.randrange(nd)
            if l == k or new[k][1] == new[l][1]:
                continue
            new[k][1], new[l][1] = new[l][1], new[k][1]
        if len({tuple(x) for x in new}) != nd:
            continue
        v = _unreached(b, N, T, invs, new, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    return darts if cur == 0 else None


def _try(b, N, d, D, rng, deadline):
    """Try groups of order N for a b-orbit lift until one yields zero cost, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(b, N, T, invs, d, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _edges(b, N, T, darts):
    """Expand darts into the explicit edge list of the lift."""
    M = b * N
    E = []
    for i, j, g in darts:
        for x in range(N):
            E.append((i * N + x, M + j * N + T[x][g]))
    return E


def _candidates(lo, hi):
    """(order, b, N) with order = 2*b*N in [lo, hi], ascending by order."""
    out = []
    for O in range(lo, hi + 1, 2):
        for b in range(1, MAX_B + 1):
            if O % (2 * b):
                continue
            N = O // (2 * b)
            if N >= 3:
                out.append((O, b, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    if D >= 2:
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

    moore = lib._moore_bound(d, D)

    # Start the window at the known record zone for the target, so the first
    # candidates reproduce the record and the next ones try to beat it.
    if (d, D) == (5, 5):
        lo = 336
    else:
        lo = best_n + 2
    lo += lo % 2
    hi = min(moore, lo + WINDOW)
    cands = _candidates(lo, hi) if lo <= hi else []

    budget = 0.5
    while time.monotonic() < deadline and cands:
        success = False
        for O, b, N in list(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            if O <= best_n:
                cands.remove((O, b, N))
                continue
            att_deadline = min(deadline, now + budget)
            res = _try(b, N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, darts = res
            consider(2 * b * N, _edges(b, N, T, darts))
            cands = [c for c in cands if c[0] > best_n]
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
