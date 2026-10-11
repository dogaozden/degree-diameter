import math
import random
import time

import lib

ITERS = 1200          # annealing steps per restart
RESTARTS = 3          # random base structures / voltage starts per group
MAX_P = 8             # largest base-graph side (p A-vertices and p B-vertices)


# ----------------------------------------------------------------------------
# Lift framework. A base bipartite multigraph has p A-vertices and p B-vertices,
# with d darts out of each A-vertex and into each B-vertex. A dart (i, j, g)
# joins A(i, x) to B(j, x*g) for every x in a finite group G of order N.
# Left multiplication by G is an automorphism that is transitive on each fibre,
# so BFS from A(i, 1) and B(j, 1) for every base vertex decides the diameter.
# With p = 1 this is the bi-Cayley family used before.
# Lift order: 2 * p * N.
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


def _random_darts(p, d, N, rng):
    """d random permutations of range(p) give the base darts; voltages are distinct within each (i, j) class."""
    darts = []
    for _ in range(d):
        s = list(range(p))
        rng.shuffle(s)
        for i in range(p):
            darts.append([i, s[i], 0])
    used = {}
    for dart in darts:
        key = (dart[0], dart[1])
        taken = used.setdefault(key, set())
        g = rng.randrange(N)
        while g in taken:
            g = rng.randrange(N)
        taken.add(g)
        dart[2] = g
    return [tuple(x) for x in darts]


def _cost(p, N, T, darts, D):
    """Total (source, vertex) pairs not within distance D, over the 2p fibre-representative sources."""
    pn = p * N
    V = 2 * pn
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        bi = i * N
        bj = pn + j * N
        for x in range(N):
            u = bi + x
            v = bj + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    sources = [i * N for i in range(p)] + [pn + j * N for j in range(p)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(p, N, T, darts, D, d, rng, iters, deadline):
    """Simulated annealing over dart voltages until every fibre source reaches all vertices within D."""
    cur = _cost(p, N, T, darts, D)
    if cur == 0:
        return darts
    for it in range(iters):
        if time.monotonic() > deadline:
            break
        k = rng.randrange(len(darts))
        i, j, g_old = darts[k]
        g = rng.randrange(N)
        if g == g_old:
            continue
        if any(dd[0] == i and dd[1] == j and dd[2] == g for dd in darts):
            continue
        new = list(darts)
        new[k] = (i, j, g)
        v = _cost(p, N, T, new, D)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
            if cur == 0:
                return darts
    return None


def _edges(p, N, T, darts):
    pn = p * N
    out = []
    for i, j, g in darts:
        for x in range(N):
            out.append((i * N + x, pn + j * N + T[x][g]))
    return out


def _attempt(n, d, D, rng, deadline):
    """Search for a valid lift on exactly n vertices, over all base sizes p and groups."""
    if n % 2:
        return None
    half = n // 2
    cands = []
    for p in range(1, MAX_P + 1):
        if half % p:
            continue
        N = half // p
        if N >= d + 1:
            cands.append((p, N))
    rng.shuffle(cands)
    for p, N in cands:
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups:
            if time.monotonic() > deadline:
                return None
            _, mul, _ = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            for _ in range(RESTARTS):
                if time.monotonic() > deadline:
                    return None
                darts = _random_darts(p, d, N, rng)
                res = _anneal(p, N, T, darts, D, d, rng, ITERS, deadline)
                if res is not None:
                    return 2 * p * N, _edges(p, N, T, res)
    return None


# ----------------------------------------------------------------------------
# Small fallback families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + max(0.5, 0.82 * time_limit - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))   # K_{d,d}, diameter 2
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    if d < 2 or D < 2:
        return best

    try:
        moore = lib.moore_bound(d, D)
        lo = best[0]
        hi = moore + 2
        while time.monotonic() < hard and hi - lo > 2:
            mid = (lo + hi) // 2
            if mid % 2:
                mid -= 1
            if mid <= lo:
                mid = lo + 2
            if mid >= hi:
                break
            now = time.monotonic()
            remaining = hard - now
            budget = min(remaining, max(3.0, 0.25 * remaining))
            res = _attempt(mid, d, D, rng, now + budget)
            if res is not None and consider(res[0], res[1]):
                lo = max(lo, mid)
            else:
                hi = mid
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
