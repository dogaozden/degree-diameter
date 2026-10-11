import itertools
import math
import random
import time

import lib

ANNEAL_ITERS = 900   # annealing steps per restart (one restart = random group + random base + random voltages)
AMAX = 8             # largest base-graph side a: the lift has 2*a*N vertices
MAX_BUDGET = 20.0    # cap on per-(a) search budget in seconds


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Voltage lifts of small bipartite multigraphs over groups (non-cyclic allowed).
#
# Base: a vertices A_i and a vertices B_j, with d darts (i, j, g) forming a
# d-regular bipartite multigraph (d random perfect matchings superposed).
# Lift over group G of order N: vertices A(i,x), B(j,y); dart (i,j,g) joins
# A(i,x) to B(j, x*g) for all x in G. Left multiplication is an automorphism,
# so checking eccentricities from the 2a sources A(i,e), B(j,e) decides the
# diameter. The lift has 2*a*N vertices and is d-regular (up to duplicates,
# which are removed before validation; duplicates never change reachability).
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


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


def _tables(m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for Z_m x|_r Z_k (cached)."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        _TABLE_CACHE[key] = (T, invs)
    return _TABLE_CACHE[key]


def _cost(a, N, T, invs, darts, D):
    """Total number of (source, vertex) pairs not within distance D, over the 2a base sources."""
    aN = a * N
    V = 2 * aN
    outA = [[] for _ in range(a)]
    inB = [[] for _ in range(a)]
    for i, j, g in darts:
        outA[i].append((j, g))
        inB[j].append((i, invs[g]))
    total = 0
    for s in range(2 * a):
        src = s * N if s < a else aN + (s - a) * N   # identity element has index 0
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outA[i]:
                        v = aN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
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


def _anneal(a, N, T, invs, d, D, rng, iters, deadline):
    """Random d-regular base multigraph, then anneal dart voltages to zero the unreached count."""
    darts = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            darts.append([i, p[i], rng.randrange(N)])
    cur = _cost(a, N, T, invs, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        temp = max(0.3, 3.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        g = rng.randrange(N)
        old = darts[k][2]
        if g == old:
            continue
        darts[k][2] = g
        v = _cost(a, N, T, invs, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _lift_graph(a, N, T, darts):
    """Materialise the lift as (n, edges) with duplicate edges removed."""
    aN = a * N
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            edges.add((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, sorted(edges)


def _attempt(a, N, d, D, rng, att_deadline):
    """Random restarts (group, base, voltages) at lift size 2*a*N until one is valid or time runs out."""
    groups = _groups(N)
    while time.monotonic() < att_deadline:
        m, k, r = rng.choice(groups)
        T, invs = _tables(m, k, r)
        darts = _anneal(a, N, T, invs, d, D, rng, ANNEAL_ITERS, att_deadline)
        if darts is None:
            continue
        n, e = _lift_graph(a, N, T, darts)
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Calibration case: incidence graph of PG(2, d-1) meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe baselines.
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
        return best[0], best[1]

    # Voltage-lift search over base sizes a = 1..AMAX.
    Moore = lib._moore_bound(d, D)
    budgets = [2.0] * (AMAX + 1)
    while True:
        if time.monotonic() >= deadline - 0.5:
            break
        tried = False
        for a in range(1, AMAX + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            # Smallest N whose lift strictly beats the current best.
            N = best[0] // (2 * a) + 1
            if 2 * a * N > Moore:
                continue
            tried = True
            att = min(deadline, now + budgets[a])
            res = _attempt(a, N, d, D, rng, att)
            if res is not None:
                consider(*res)
            else:
                budgets[a] = min(budgets[a] * 1.5, MAX_BUDGET)
        if not tried:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
