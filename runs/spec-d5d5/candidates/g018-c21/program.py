import itertools
import math
import random
import time

import lib

MAX_GROUPS = 10     # groups tried per (n, a) within one attempt
ITERS = 400         # annealing steps per group try
MAX_A = 3           # max number of A-orbits (and B-orbits) in the base graph
WINDOW = 30         # how far above the current best order each pass looks


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
# NEW CONSTRUCTION: multi-orbit voltage lifts over non-cyclic groups.
#
# Base graph: a "A-orbits" A_0..A_{a-1} and a "B-orbits" B_0..B_{a-1}, each
# orbit a copy of a finite group G of order N. Base multigraph is d-regular
# (each A_i has d darts, each B_j receives d darts). A dart (i, j, g) joins
# A_{i,x} -- B_{j, x*g} for all x in G. The lift has 2*a*N vertices, is bipartite
# and has max degree d by construction, so only diameter needs checking.
#
# Left multiplication by h in G is an automorphism, so the eccentricities of
# the 2a orbit representatives A_{i,e}, B_{j,e} decide the diameter. This is
# a generalization of the bi-Cayley search (a = 1) to several orbits, which
# gives many more degrees of freedom at the same order.
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


def _cost(N, a, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, over the 2a orbit representatives."""
    aN = a * N
    V = 2 * aN
    dA = [[] for _ in range(a)]
    dB = [[] for _ in range(a)]
    for i, j, g in darts:
        dA[i].append((j, g))
        dB[j].append((i, invs[g]))
    sources = [i * N for i in range(a)] + [(a + j) * N for j in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = (a + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, a, T, invs, pairs, D, rng, iters, deadline):
    """Anneal the dart group elements so that the lift has diameter <= D.

    Darts sharing an (i, j) pair need distinct group elements, otherwise edges repeat.
    """
    darts = [[i, j, -1] for i, j in pairs]

    def clash(k, g):
        i, j, _ = darts[k]
        for k2, (i2, j2, g2) in enumerate(darts):
            if k2 != k and i2 == i and j2 == j and g2 == g:
                return True
        return False

    for k in range(len(darts)):
        while True:
            g = rng.randrange(N)
            if not clash(k, g):
                darts[k][2] = g
                break

    cur = _cost(N, a, T, invs, darts, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        g = rng.randrange(N)
        if g == darts[k][2] or clash(k, g):
            continue
        old = darts[k][2]
        darts[k][2] = g
        v = _cost(N, a, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _attempt(n, d, D, rng, deadline):
    """Try (a, group) choices giving 2*a*N = n vertices until one works or time runs out."""
    opts = [a for a in range(1, MAX_A + 1) if n % (2 * a) == 0 and n // (2 * a) >= d]
    rng.shuffle(opts)
    for a in opts:
        N = n // (2 * a)
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                return None
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(order)] for x in range(order)]
            invs = [inv(g) for g in range(order)]
            # Random d-regular base multigraph between a A-orbits and a B-orbits.
            slots = [j for j in range(a) for _ in range(d)]
            rng.shuffle(slots)
            pairs = [(i, slots[i * d + t]) for i in range(a) for t in range(d)]
            darts = _anneal(order, a, T, invs, pairs, D, rng, ITERS, deadline)
            if darts is not None:
                return order, a, T, darts
    return None


def _edges(N, a, T, darts):
    """Expand base darts into the lifted edge list."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (a + j) * N + T[x][g]))
    return 2 * a * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    Mb = lib._moore_bound(d, D)
    budget = 1.0
    while time.monotonic() < deadline and best_n < Mb:
        first = best_n + 1
        if first % 2:
            first += 1
        last = min(Mb, best_n + WINDOW)
        found = False
        for n in range(first, last + 1, 2):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(n, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            N, a, T, darts = res
            nn, edges = _edges(N, a, T, darts)
            consider(nn, edges)
            found = True
        if not found:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
