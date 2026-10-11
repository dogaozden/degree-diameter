import itertools
import math
import random
import time

import lib

KMAX = 6          # base-graph sizes per side tried: 1..KMAX
PER_K = 6         # smallest feasible group orders kept per base size
ITERS = 600       # annealing steps per (group, base) attempt
MAX_GROUPS = 30   # groups tried per attempt
ROUND_BUDGET = 0.3


# ----------------------------------------------------------------------------
# Safe baseline families (used as fallbacks; all checked with lib.is_valid).
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
# New construction: bipartite voltage lifts with a SMALL base graph.
#
# Base: kb A-vertices and kb B-vertices, every base vertex of degree d
# (random configuration-model pairing, parallel darts allowed).
# Each dart (u, v, g) lifts to edges (A,u,x) -- (B,v,x*g) over a group G
# of order N. Total order 2*kb*N, degree d.
#
# Left multiplication by G is an automorphism, so the diameter is the max
# eccentricity over the 2*kb sources (A,u,e) and (B,v,e).
# Search: simulated annealing over dart voltages, for many groups
# (semidirect products Z_m x| Z_k of order N).
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


def _random_base(kb, d, rng):
    """Random d-regular bipartite multigraph on kb + kb base vertices, as (u, v) darts."""
    a = [u for u in range(kb) for _ in range(d)]
    b = a[:]
    rng.shuffle(b)
    return list(zip(a, b))


def _cost(kb, N, mul, invtab, darts, D):
    """Unreached (source, vertex) pairs over the 2*kb base sources, plus duplicate-dart penalty."""
    nh = kb * N
    out = [[] for _ in range(kb)]
    inn = [[] for _ in range(kb)]
    seen = set()
    dup = 0
    for (u, v, g) in darts:
        t = (u, v, g)
        if t in seen:
            dup += 1
        else:
            seen.add(t)
        out[u].append((v, g))
        inn[v].append((u, invtab[g]))

    total = 0
    sources = [u * N for u in range(kb)] + [nh + v * N for v in range(kb)]
    for src in sources:
        mark = bytearray(2 * nh)
        mark[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                if w < nh:
                    u, x = divmod(w, N)
                    for v, g in out[u]:
                        t = nh + v * N + mul(x, g)
                        if not mark[t]:
                            mark[t] = 1
                            nxt.append(t)
                else:
                    v, y = divmod(w - nh, N)
                    for u, gi in inn[v]:
                        t = u * N + mul(y, gi)
                        if not mark[t]:
                            mark[t] = 1
                            nxt.append(t)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * nh - count
    return total + dup * (2 * nh)


def _anneal(kb, N, mul, invtab, darts, D, rng, iters, deadline):
    """Anneal dart voltages until every source reaches everything within D."""
    cur = _cost(kb, N, mul, invtab, darts, D)
    for it in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            break
        i = rng.randrange(len(darts))
        u, v, old_g = darts[i]
        g = rng.randrange(N)
        if g == old_g:
            continue
        darts[i] = (u, v, g)
        c = _cost(kb, N, mul, invtab, darts, D)
        temp = max(0.3, 4.0 * (1.0 - it / iters))
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            darts[i] = (u, v, old_g)
    return cur == 0


def _attempt(kb, N, d, D, rng, deadline):
    """Try groups of order N with random bases until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        invtab = [inv(g) for g in range(N)]
        pairs = _random_base(kb, d, rng)
        darts = [(u, v, rng.randrange(N)) for u, v in pairs]
        if _anneal(kb, N, mul, invtab, darts, D, rng, ITERS, deadline):
            return kb, N, mul, darts
    return None


def _lift_edges(kb, N, mul, darts):
    """Expand the voltage lift into (n, edges)."""
    nh = kb * N
    edges = set()
    for u, v, g in darts:
        for x in range(N):
            a = u * N + x
            b = nh + v * N + mul(x, g)
            edges.add((a, b))
    return 2 * nh, sorted(edges)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        # K2 is bipartite, has diameter 1, and has max degree 1 <= d.
        return 2, [(0, 1)]

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe baselines.
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New search: small-base voltage lifts over semidirect products.
    moore = lib._moore_bound(d, D)
    cands = []
    for kb in range(1, KMAX + 1):
        lo = best[0] // (2 * kb) + 1
        hi = moore // (2 * kb)
        count = 0
        for N in range(max(1, lo), hi + 1):
            if count >= PER_K:
                break
            cands.append((2 * kb * N, kb, N))
            count += 1
    cands.sort()

    budget = ROUND_BUDGET
    while cands and time.monotonic() < deadline:
        for tot, kb, N in list(cands):
            if time.monotonic() >= deadline:
                break
            if tot <= best[0]:
                continue
            att = min(deadline, time.monotonic() + budget)
            res = _attempt(kb, N, d, D, rng, att)
            if res is not None:
                kb_, N_, mul, darts = res
                n, e = _lift_edges(kb_, N_, mul, darts)
                consider(n, e)
        budget *= 1.6
        cands = [c for c in cands if c[0] > best[0]]

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
