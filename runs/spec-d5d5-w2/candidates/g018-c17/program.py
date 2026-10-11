import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: PG(2,q) for D = 3 and W(q) for D >= 4.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW HELPER: bitset ball growth for cyclic bi-Cayley lifts.
#
# Cyclic lift on Z_N with connection set S: A_x ~ B_{x+s} for s in S.
# Encode the reached sets of A and B as N-bit integers. One BFS layer is
#   new_B = OR_s rot(A, s),    new_A = OR_s rot(B, -s),
# where rot(X, s) shifts every bit x to x+s mod N. This replaces per-vertex
# BFS loops with d big-integer rotations per layer, which is much faster for
# the hill climb. Translation symmetry means sources A_0 and B_0 suffice.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cyc_cost(N, S, D, limit=_BIG):
    """Number of (source, vertex) pairs unreached within D, from A_0 and B_0. Zero means valid."""
    full = (1 << N) - 1
    neg = [(-s) % N for s in S]

    def rot(x, s):
        if s == 0:
            return x
        return ((x << s) | (x >> (N - s))) & full

    total = 0
    for src_is_a in (True, False):
        a = 1 if src_is_a else 0
        b = 0 if src_is_a else 1
        for _ in range(D):
            na, nb = a, b
            for s in S:
                nb |= rot(a, s)
            for s in neg:
                na |= rot(b, s)
            if na == a and nb == b:
                break
            a, b = na, nb
        total += 2 * N - a.bit_count() - b.bit_count()
        if total > limit:
            return total
    return total


# ----------------------------------------------------------------------------
# General (semidirect) bi-Cayley lifts, using explicit BFS over group tables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
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
    """Cached (T, invs) for the group Z_m x|_r Z_k, with T[x][g] = x*g."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _grp_cost(N, T, invs, S, D, limit=_BIG):
    """Unreached pairs from A_0 and B_0 for the bi-Cayley graph A_x ~ B_{x*g}, g in S."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
        if total > limit:
            return total
    return total


# ----------------------------------------------------------------------------
# Shared hill climb over connection sets (identity fixed as one dart, WLOG).
# ----------------------------------------------------------------------------

def _climb(N, d, rng, cost, iters, deadline, stall_limit=400):
    """Hill-climb S (|S| = d, 0 in S) to zero cost; sideways moves allowed, restart on stall."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, cost(S, _BIG)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = cost(S2, cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > stall_limit:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_semidirect(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, invs = _tables(m, k, r)
        S = _climb(N, d, rng,
                   lambda S_, lim: _grp_cost(N, T, invs, S_, D, lim),
                   1500, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

CYC_ITERS = 4000
N_WINDOW = 6


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: bi-Cayley lifts just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)

        if rng.random() < 0.6:
            # Cyclic lift, evaluated with bitset ball growth.
            S = _climb(N, d, rng,
                       lambda S_, lim: _cyc_cost(N, S_, D, lim),
                       CYC_ITERS, deadline)
            if S is not None:
                edges = [(x, N + (x + s) % N) for x in range(N) for s in S]
                consider(2 * N, edges)
        else:
            # Semidirect lift over a non-cyclic group when one exists.
            res = _search_semidirect(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
