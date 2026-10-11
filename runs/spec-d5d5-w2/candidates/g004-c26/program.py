import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters.
#
# New construction: "multi-base voltage lift". A base graph with b vertices on
# each side (b = 1, 2, 3) and d darts per base vertex is lifted over a finite
# group G of order N. Vertex A_{i,x} is joined to B_{j, x*g} for every dart
# (i, j, g). The darts for each pair (i, j) are a set of distinct group
# elements, and the dart multiplicity matrix is a sum of d permutation matrices,
# so the lift is simple, bipartite and exactly d-regular with 2*b*N vertices.
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from the 2b base identities. Annealing minimizes the number of unreached
# (source, vertex) pairs.
# ----------------------------------------------------------------------------

ITERS = 500          # annealing steps per (group, base) try
T_HOT = 6.0          # initial temperature (unreached-pair units)
T_COLD = 0.3         # final temperature
MAX_GROUPS = 10      # groups tried per (order, b) attempt
BUDGET0 = 1.0        # seconds per order attempt in the first pass
BUDGET_CAP = 6.0     # cap on per-attempt seconds
WINDOW0 = 6          # orders searched just below the Moore-based top


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 4), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lift search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_matrix(b, d, rng):
    """b x b nonnegative integer matrix with all row and column sums equal to d.

    Built as a sum of d random permutation matrices, so the lift is d-regular.
    """
    c = [[0] * b for _ in range(b)]
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            c[i][perm[i]] += 1
    return c


def _init_darts(N, b, c, rng):
    """Dart sets: for each (i, j) with c[i][j] > 0, a set of c[i][j] distinct group elements."""
    darts = {}
    for i in range(b):
        for j in range(b):
            if c[i][j]:
                darts[(i, j)] = rng.sample(range(N), c[i][j])
    return darts


def _cost(N, b, T, darts, D):
    """Number of (base source, vertex) pairs at distance more than D."""
    V = 2 * b * N
    adj = [[] for _ in range(V)]
    for (i, j), gs in darts.items():
        ai = i * N
        bj = b * N + j * N
        for g in gs:
            for x in range(N):
                a = ai + x
                y = bj + T[x][g]
                adj[a].append(y)
                adj[y].append(a)
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(N, b, T, c, d, D, rng, iters, deadline):
    """Simulated annealing over dart sets to make the lift have diameter <= D."""
    darts = _init_darts(N, b, c, rng)
    keys = list(darts.keys())
    cur = _cost(N, b, T, darts, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        key = keys[rng.randrange(len(keys))]
        lst = darts[key]
        t = rng.randrange(len(lst))
        g = rng.randrange(N)
        if g in lst:
            continue
        nl = lst[:]
        nl[t] = g
        nd = dict(darts)
        nd[key] = nl
        v = _cost(N, b, T, nd, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = nd, v
    return darts if cur == 0 else None


def _attempt(N, b, d, D, rng, deadline):
    """Try several groups of order N for base size b; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        try:
            _, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        c = _random_matrix(b, d, rng)
        darts = _anneal(N, b, T, c, d, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _to_graph(N, b, T, darts):
    """Expand the base-lift description into (n, edges)."""
    edges = []
    for (i, j), gs in darts.items():
        bj = b * N + j * N
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, bj + T[x][g]))
    return 2 * b * N, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, min(0.8 * time_limit, time_limit - 4.0))
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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Baselines (each guarded so a failure cannot lose the fallback).
    try:
        if D >= 2 and d >= 1:
            consider(*lib.haar_graph(d, range(d)))
    except Exception:
        pass
    try:
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(*lib.araujo_lopez_graph(d - 2))
    except Exception:
        pass
    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
    except Exception:
        pass
    try:
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    if d < 2 or D < 2:
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best

    moore = lib.moore_bound(d, D)
    # Base sizes b with room for the search (need N >= d + 1).
    bl = [b for b in (2, 3, 1) if moore // (2 * b) >= d + 1]
    if not bl:
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best
    nmax = {b: moore // (2 * b) for b in bl}

    budget = BUDGET0
    window = WINDOW0
    while time.monotonic() < deadline:
        progressed = False
        active = False
        for b in bl:
            if time.monotonic() >= deadline:
                break
            lo_n = max(d + 1, best_n // (2 * b) + 1)
            top = nmax[b]
            if lo_n > top:
                continue
            active = True
            floor_n = max(lo_n, top - window)
            for N in range(top, floor_n - 1, -1):
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _attempt(N, b, d, D, rng, min(deadline, now + budget))
                if res is None:
                    continue
                T, darts = res
                n, e = _to_graph(N, b, T, darts)
                consider(n, e)
                progressed = True
                break
        if not active:
            break
        if not progressed:
            budget = min(BUDGET_CAP, budget * 1.5)
            window *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
