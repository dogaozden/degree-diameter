import itertools
import math
import random
import time

import lib

K_MAX = 4                 # base graphs with 2k vertices per fiber family (k A-fibers, k B-fibers)
ITERS = 1500              # annealing steps per attempt
MAX_GROUPS_PER_N = 40     # groups tried for one (k, N) within an attempt
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generalized voltage lifts over finite groups (non-cyclic groups allowed).
#
# Base: k A-vertices and k B-vertices, each of degree d (multigraph, parallel
# darts allowed only with distinct voltages). Lift: fiber A_i = {i*N + x},
# fiber B_j = {kN + j*N + y}. Dart (i, j, g) joins A(i,x) to B(j, x*g).
# Left multiplication is an automorphism, so eccentricities are constant on
# each fiber: it suffices to BFS from A(i, e) and B(j, e) for all i, j.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic included)."""
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
    """Cached multiplication table T[x][g] = x*g for the group Z_m x|_r Z_k."""
    key = (m, k, r)
    if key not in _TABLE_CACHE:
        if len(_TABLE_CACHE) > 40:
            _TABLE_CACHE.clear()
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        _TABLE_CACHE[key] = (order, T)
    return _TABLE_CACHE[key]


def _eval(k, N, T, darts, D):
    """Total number of (source, vertex) pairs at distance > D, over one source per fiber."""
    V = 2 * k * N
    bB = k * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        base_a = i * N
        off = bB + j * N
        for x in range(N):
            a = base_a + x
            b = off + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    srcs = [i * N for i in range(k)] + [bB + j * N for j in range(k)]
    for s in srcs:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _init_darts(k, N, d, rng):
    """Random base: each A_i gets d darts, each B_j receives d darts; parallel darts get distinct voltages."""
    targets = [j for j in range(k) for _ in range(d)]
    rng.shuffle(targets)
    used = {}
    out = []
    for i in range(k):
        for t in range(d):
            j = targets[i * d + t]
            s = used.setdefault((i, j), set())
            if len(s) >= N:
                return None
            while True:
                g = rng.randrange(N)
                if g not in s:
                    break
            s.add(g)
            out.append((i, j, g))
    return out


def _anneal(k, N, T, d, D, rng, iters, deadline):
    darts = _init_darts(k, N, d, rng)
    if darts is None:
        return None
    cur = _eval(k, N, T, darts, D)
    if cur == 0:
        return darts
    L = len(darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        t = rng.randrange(L)
        i, j, g = darts[t]
        ng = rng.randrange(N)
        if ng == g:
            continue
        clash = False
        for q in range(L):
            if q != t and darts[q][0] == i and darts[q][1] == j and darts[q][2] == ng:
                clash = True
                break
        if clash:
            continue
        old = darts[t]
        darts[t] = (i, j, ng)
        v = _eval(k, N, T, darts, D)
        temp = 2.0 * (1.0 - it / iters) + 0.3
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[t] = old
    return darts if cur == 0 else None


def _attempt_lift(k, N, d, D, rng, deadline):
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        order, T = _tables(m, kk, r)
        darts = _anneal(k, order, T, d, D, rng, ITERS, deadline)
        if darts is not None:
            return order, T, darts
    return None


def _lift_edges(k, N, T, darts):
    bB = k * N
    edges = []
    for i, j, g in darts:
        off = bB + j * N
        for x in range(N):
            edges.append((i * N + x, off + T[x][g]))
    return 2 * k * N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget_total
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

    # Record-matching case for D = 3.
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

    # Candidate (total_vertices, k, N): total = 2*k*N must beat the current best.
    cands = []
    for k in range(1, K_MAX + 1):
        for N in range(max(d + 1, 2), moore // (2 * k) + 1):
            tot = 2 * k * N
            if best_n < tot <= moore:
                cands.append((tot, k, N))
    cands.sort()

    budget = 0.3
    while time.monotonic() < deadline and cands:
        success = False
        for tot, k, N in list(cands):
            if tot <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            att_dl = min(deadline, now + budget)
            res = _attempt_lift(k, N, d, D, rng, att_dl)
            if res is None:
                continue
            order, T, darts = res
            n, edges = _lift_edges(k, order, T, darts)
            consider(n, edges)
            cands = [c for c in cands if c[0] > best_n]
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
