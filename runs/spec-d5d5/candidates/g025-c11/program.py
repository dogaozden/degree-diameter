import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured constructions for D = 3 and D = 4 (projective planes and
# generalized quadrangles). These are used only when they apply.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main engine for D >= 5: bit-parallel cyclic bi-Cayley search.
#
# Vertices: A_x = x, B_y = N + y, with x, y in Z_N and A_x ~ B_{x+s} for s in S.
# Translation by Z_N and the side-swap automorphism mean that checking the
# distances from A_0 alone certifies diameter D for the whole graph.
# Sets of Z_N are Python ints used as bitmasks, so one BFS level costs d
# cyclic rotations rather than a per-vertex loop. This is far faster than
# per-vertex BFS, which allows many more candidate connection sets.
# ----------------------------------------------------------------------------

CYC_STALL = 400       # restart a cyclic hill-climb after this many non-improving steps
SEMI_MAX_GROUPS = 8   # non-abelian groups tried per order
SEMI_ITERS = 800      # hill-climb steps per restart (non-abelian)
SEMI_STALL = 200
WINDOW = 6            # candidate orders above the current lower bound
_TABLE_CACHE = {}


def _cyclic_cost(N, D, S):
    """Number of vertices not within distance D of A_0 in the cyclic bi-Cayley graph on S."""
    full = (1 << N) - 1
    pos = list(S)
    neg = [(N - s) % N for s in S]

    def rot(m, k):
        if k == 0:
            return m
        return ((m << k) | (m >> (N - k))) & full

    seen_a = 1
    seen_b = 0
    fa = 1
    fb = 0
    for t in range(D):
        if t % 2 == 0:
            nb = 0
            for s in pos:
                nb |= rot(fa, s)
            nb &= full & ~seen_b
            seen_b |= nb
            fb = nb
        else:
            na = 0
            for s in neg:
                na |= rot(fb, s)
            na &= full & ~seen_a
            seen_a |= na
            fa = na
    return 2 * N - seen_a.bit_count() - seen_b.bit_count()


def _cyclic_search(N, d, D, rng, deadline):
    """Hill-climb S (containing 0 WLOG) to zero unreached vertices, with restarts."""
    if N < d or d < 3:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        c = _cyclic_cost(N, D, S)
        stall = 0
        while c > 0 and stall < CYC_STALL and time.monotonic() < deadline:
            i = rng.randrange(1, d)
            v = rng.randrange(1, N)
            if v in S:
                stall += 1
                continue
            S2 = S[:]
            S2[i] = v
            c2 = _cyclic_cost(N, D, S2)
            if c2 < c:
                stall = 0
            else:
                stall += 1
            if c2 <= c:
                S, c = S2, c2
        if c == 0:
            return S
    return None


def _cyclic_edges(N, S):
    """Edges of the cyclic bi-Cayley lift: A_x ~ B_{x+s}."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Non-abelian bi-Cayley lifts over Z_m x|_r Z_k (complement to the cyclic search).
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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
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
    return total


def _semidirect_search(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid bi-Cayley lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:SEMI_MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k, r)
        while time.monotonic() < deadline:
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = _unreached(N, T, invs, S, D)
            stall = 0
            for _ in range(SEMI_ITERS):
                if cur == 0 or time.monotonic() > deadline or stall > SEMI_STALL:
                    break
                i = rng.randrange(1, d)
                c = rng.randrange(1, N)
                if c in S:
                    continue
                S2 = S[:]
                S2[i] = c
                v = _unreached(N, T, invs, S2, D)
                stall = 0 if v < cur else stall + 1
                if v <= cur:
                    S, cur = S2, v
            if cur == 0:
                return T, S
            break  # one restart per group keeps the time spread across groups
    return None


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
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # d = 2: the even cycle C_{2D} is bipartite with diameter D.
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: aim above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(WINDOW)
        if N > moore // 2:
            continue
        remaining = deadline - time.monotonic()
        sub = time.monotonic() + max(0.5, 0.25 * remaining)
        sub = min(sub, deadline)

        if rng.random() < 0.7:
            S = _cyclic_search(N, d, D, rng, sub)
            if S is not None:
                consider(2 * N, _cyclic_edges(N, S))
        else:
            res = _semidirect_search(d, D, N, rng, sub)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
