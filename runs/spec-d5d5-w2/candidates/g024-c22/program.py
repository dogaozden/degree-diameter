import itertools
import math
import random
import time

import lib

T_HOT = 12.0            # initial annealing temperature (unreached-pair units)
T_COLD = 0.3            # final annealing temperature
ITERS = 500             # annealing steps per restart
DUP_PENALTY = 60        # cost per duplicate dart (would create a duplicate edge)
START_BUDGET = 2.0      # seconds per (a, N) attempt in the first round
MAX_BUDGET = 10.0       # cap on per-attempt seconds
# Number of base vertices per side. a = 1 is a plain bi-Cayley graph;
# a >= 2 is a voltage lift over a bipartite base multigraph with a + a vertices.
A_CHOICES = (2, 3, 4, 1, 5, 6, 8)


# ----------------------------------------------------------------------------
# Fallback families (fast, validated before use).
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
# Multi-orbit voltage lifts over finite groups of order N.
#
# Base graph: a A-vertices and a B-vertices, each of degree d. Dart i joins
# A-vertex u = i // d to B-vertex Bv[i] with voltage G[i] in the group G.
# Lift: A(u, x) ~ B(v, x * g) for every x in G. Left multiplication is an
# automorphism, so the eccentricity of A(u, e) and B(v, e) determines the
# diameter, and only 2a BFS runs are needed to check the lift.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) for all groups Z_m x|_r Z_k of order N (cyclic included)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(N, m, k, r):
    """Multiplication table T[x][g] = x * g for the group Z_m x|_r Z_k."""
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(N)] for x in range(N)]


def _cost(a, N, D, d, Bv, G, T):
    """Number of (source, vertex) pairs at distance > D, plus duplicate-dart penalties."""
    side = a * N
    V = 2 * side
    adj = [[] for _ in range(V)]
    seen = set()
    dups = 0
    for i in range(a * d):
        u = i // d
        v = Bv[i]
        g = G[i]
        key = (u, v, g)
        if key in seen:
            dups += 1
            continue
        seen.add(key)
        bu = u * N
        bv = side + v * N
        for x in range(N):
            p = bu + x
            q = bv + T[x][g]
            adj[p].append(q)
            adj[q].append(p)
    total = 0
    sources = [u * N for u in range(a)] + [side + v * N for v in range(a)]
    for s in sources:
        mark = bytearray(V)
        mark[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                for y in adj[x]:
                    if not mark[y]:
                        mark[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total + DUP_PENALTY * dups


def _anneal(a, N, D, d, T, rng, deadline):
    """Anneal voltages and base endpoints to zero unreached pairs. Returns (Bv, G) or None."""
    M = a * d
    Bv = [v for v in range(a) for _ in range(d)]
    rng.shuffle(Bv)
    G = [rng.randrange(N) for _ in range(M)]
    cur = _cost(a, N, D, d, Bv, G, T)
    for it in range(ITERS):
        if cur == 0:
            return Bv, G
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        if rng.random() < 0.5:
            i = rng.randrange(M)
            old = G[i]
            ng = rng.randrange(N)
            if ng == old:
                continue
            G[i] = ng
            new = _cost(a, N, D, d, Bv, G, T)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                G[i] = old
        else:
            i = rng.randrange(M)
            j = rng.randrange(M)
            if Bv[i] == Bv[j]:
                continue
            Bv[i], Bv[j] = Bv[j], Bv[i]
            new = _cost(a, N, D, d, Bv, G, T)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                Bv[i], Bv[j] = Bv[j], Bv[i]
    if cur == 0:
        return Bv, G
    return None


def _attempt(a, N, d, D, rng, end, cache):
    """Try random groups of order N with random voltages until success or time runs out."""
    groups = _groups(N)
    while time.monotonic() < end:
        m, k, r = rng.choice(groups)
        key = (N, m, k, r)
        T = cache.get(key)
        if T is None:
            T = _table(N, m, k, r)
            cache[key] = T
        res = _anneal(a, N, D, d, T, rng, end)
        if res is not None:
            return res[0], res[1], T
    return None


def _edges(a, N, d, T, Bv, G):
    """Expand the base graph and voltages into the full lift (n, edges)."""
    side = a * N
    E = []
    for i in range(a * d):
        u = i // d
        v = Bv[i]
        g = G[i]
        for x in range(N):
            E.append((u * N + x, side + v * N + T[x][g]))
    return 2 * side, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Cycle C_{2D}: optimal for degree 2.
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Baseline families.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Multi-orbit lift search for the remaining time.
    moore = lib.moore_bound(d, D)
    nextN = {}
    for a in A_CHOICES:
        nextN[a] = max(d, best_n // (2 * a) + 1)
    cache = {}
    budget = START_BUDGET
    while time.monotonic() < deadline:
        tried = False
        success = False
        for a in A_CHOICES:
            if time.monotonic() >= deadline:
                break
            nextN[a] = max(nextN[a], best_n // (2 * a) + 1, d)
            N = nextN[a]
            if 2 * a * N > moore:
                continue
            tried = True
            end = min(deadline, time.monotonic() + budget)
            res = _attempt(a, N, d, D, rng, end, cache)
            if res is None:
                continue
            Bv, G, T = res
            n, edges = _edges(a, N, d, T, Bv, G)
            consider(n, edges)
            nextN[a] = N + 1
            success = True
        if not tried:
            break
        if not success:
            budget = min(MAX_BUDGET, budget * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
