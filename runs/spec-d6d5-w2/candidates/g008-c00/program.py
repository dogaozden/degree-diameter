import itertools
import math
import random
import time

import lib

# Tabu search parameters for bi-Cayley voltage lifts.
SAMPLE = 14     # random candidate moves evaluated per tabu iteration
TENURE = 6      # iterations an removed connection element stays forbidden
STALL = 300     # non-improving iterations before a random restart


# ----------------------------------------------------------------------------
# Classical baselines (fallbacks for every D, and the only path for D <= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over non-abelian groups (Z_m x| Z_k), found by tabu search.
#
# Group G with multiplication table M (right action) and inverse table I.
# Connection set S (|S| = d, distinct). Vertices: A_x = x, B_y = G + y.
# Edges: A_x -- B_{x*s} for s in S.
# Left translations are automorphisms, so checking the balls of A_e and B_e
# within distance D is equivalent to diameter <= D.
# ----------------------------------------------------------------------------

def _unreached(src, S, Si, G, M, D):
    """Number of vertices not within distance D of src. Si = inverses of S."""
    seen = bytearray(2 * G)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = M[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = M[u - G]
                for s in Si:
                    v = row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return 2 * G - count


def _cost(T, G, M, I, D):
    """Zero iff the bi-Cayley graph with connection set T has diameter <= D."""
    Ti = [I[s] for s in T]
    return _unreached(0, T, Ti, G, M, D) + _unreached(G, T, Ti, G, M, D)


def _group_tables(G, rng):
    """Multiplication and inverse tables for a random semidirect product of order G."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            opts.append((m, 1, 1))  # cyclic group Z_G
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    nonab = [o for o in opts if o[1] > 1 and o[2] != 1]
    pool = nonab if (nonab and rng.random() < 0.7) else opts
    m, k, r = rng.choice(pool)
    _, mul, _ = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(G)] for x in range(G)]
    I = [0] * G
    for s in range(G):
        I[s] = M[s].index(0)  # x with s*x = identity
    return M, I


def _tabu(d, D, G, M, I, rng, deadline):
    """Tabu search over connection sets of size d. Returns S with cost 0, or None."""
    S = rng.sample(range(G), d)
    cost = _cost(S, G, M, I, D)
    best = cost
    stall = 0
    tabu = {}
    it = 0
    while cost:
        it += 1
        if time.monotonic() > deadline:
            return None
        if stall > STALL:
            S = rng.sample(range(G), d)
            cost = _cost(S, G, M, I, D)
            best = cost
            stall = 0
            tabu = {}
            continue
        inS = set(S)
        move = None
        mc = None
        for _ in range(SAMPLE):
            pos = rng.randrange(d)
            t = rng.randrange(G)
            if t in inS:
                continue
            T = S[:]
            T[pos] = t
            c = _cost(T, G, M, I, D)
            if tabu.get(t, -1) > it and c >= best:
                continue
            if mc is None or c < mc:
                mc = c
                move = (pos, t)
        if move is None:
            continue
        pos, t = move
        tabu[S[pos]] = it + TENURE
        S[pos] = t
        cost = mc
        if cost < best:
            best = cost
            stall = 0
        else:
            stall += 1
    return S


def _search_bicayley(d, D, best_n, rng, start, deadline, consider):
    """Search group orders near and above the record band, one tabu attempt per group draw."""
    half = max(1, lib.moore_bound(d, D) // 2)
    hi = max(2, int(0.95 * half))
    floor = max(best_n // 2 + 1, int(0.42 * half))
    total = max(1.0, deadline - start)
    slice_len = max(2.0, 0.1 * total)
    while time.monotonic() < deadline:
        G = min(hi, max(floor, 2) + int(rng.expovariate(1.0 / 12.0)))
        if G < d + 1:
            G = d + 1
        M, I = _group_tables(G, rng)
        att_deadline = min(deadline, time.monotonic() + slice_len)
        S = _tabu(d, D, G, M, I, rng, att_deadline)
        if S is not None:
            edges = [(x, G + M[x][s]) for x in range(G) for s in S]
            consider(2 * G, edges)
            floor = max(floor, G + 1)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New main family for D >= 5: bi-Cayley lifts over non-abelian groups.
    if D >= 5 and d >= 2:
        _search_bicayley(d, D, best_n, rng, start, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
