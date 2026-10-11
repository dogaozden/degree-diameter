import itertools
import math
import random
import time

import lib

ITERS = 1500                 # annealing steps per (group, base structure) try
MAX_GROUPS_PER_ATTEMPT = 40  # groups tried per attempt before giving up
BASES = (2, 3, 4, 5, 6, 1)   # base-graph sizes per side, tried in rotation


# ----------------------------------------------------------------------------
# Safe baseline families (kept as fallbacks; every result is checked by lib).
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
# Non-bi-Cayley search: lifts of a bipartite base multigraph with b vertices
# per side over a finite group G of order M (semidirect products Z_m x| Z_k).
#
# Vertices: A_{i,x} = i*M + x, B_{j,y} = b*M + j*M + y.
# Dart (i, j, g) gives edges A_{i,x} -- B_{j, x*g} for all x in G.
# Left multiplication by G is an automorphism, so BFS from one vertex per
# fibre (x = identity) decides the diameter. The base is a sum of d random
# permutation matrices, so every base vertex has degree d.
# Parallel darts between the same (i, j) must use distinct voltages.
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


def _random_structure(b, d, rng):
    """Base darts as (i, j) pairs: a sum of d random permutations of range(b)."""
    pairs = []
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            pairs.append((i, perm[i]))
    return pairs


def _unreached(b, M, T, invs, darts, D):
    """Count (source, vertex) pairs at distance > D, with one source per base vertex."""
    adjA = [[] for _ in range(b)]
    adjB = [[] for _ in range(b)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, invs[g]))
    bM = b * M
    N = 2 * bM
    sources = [i * M for i in range(b)] + [bM + j * M for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bM:
                    i, x = divmod(u, M)
                    row = T[x]
                    for j, g in adjA[i]:
                        v = bM + j * M + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bM, M)
                    row = T[y]
                    for i2, h in adjB[j]:
                        v = i2 * M + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _anneal(b, M, T, invs, pairs, D, rng, iters, deadline):
    """Anneal dart voltages (structure fixed) to zero unreached pairs; return darts or None."""
    K = len(pairs)
    same = [[q for q in range(K) if q != k and pairs[q] == pairs[k]] for k in range(K)]
    gs = [0] * K
    for pr in set(pairs):
        idx = [k for k in range(K) if pairs[k] == pr]
        vals = rng.sample(range(M), len(idx))
        for k, v in zip(idx, vals):
            gs[k] = v

    def darts():
        return [(pairs[k][0], pairs[k][1], gs[k]) for k in range(K)]

    cur = _unreached(b, M, T, invs, darts(), D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        k = rng.randrange(K)
        g = rng.randrange(M)
        if any(gs[q] == g for q in same[k]):
            continue
        old = gs[k]
        gs[k] = g
        v = _unreached(b, M, T, invs, darts(), D)
        temp = max(0.1, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    if cur == 0:
        return darts()
    return None


def _attempt(b, M, d, D, rng, deadline):
    """Try groups of order M with random base structures until a lift has diameter <= D."""
    groups = _groups(M)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(M)] for x in range(M)]
        invs = [inv(g) for g in range(M)]
        pairs = _random_structure(b, d, rng)
        darts = _anneal(b, M, T, invs, pairs, D, rng, ITERS, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(b, M, T, darts):
    """Expand darts into the simple bipartite graph on 2*b*M vertices."""
    bM = b * M
    edges = []
    for i, j, g in darts:
        for x in range(M):
            edges.append((i * M + x, bM + j * M + T[x][g]))
    return 2 * bM, edges


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

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Safe baseline: K_{d,d} has diameter 2 <= D.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib._moore_bound(d, D)
    budget = 1.0
    while time.monotonic() < deadline and best_n < moore:
        improved = False
        attempted = False
        for b in BASES:
            now = time.monotonic()
            if now >= deadline:
                break
            M = max(d, -(-(best_n + 1) // (2 * b)))
            if 2 * b * M > moore:
                continue
            attempted = True
            att_deadline = min(deadline, now + budget)
            res = _attempt(b, M, d, D, rng, att_deadline)
            if res is None:
                continue
            T, darts = res
            n, e = _lift_edges(b, M, T, darts)
            before = best_n
            consider(n, e)
            if best_n > before:
                improved = True
        if not attempted:
            break
        if not improved:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
