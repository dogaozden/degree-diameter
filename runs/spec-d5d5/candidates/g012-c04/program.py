import math
import random
import time

import lib

MAX_GROUPS = 30     # groups tried per (block count a, group order N) attempt
ITERS = 1200        # annealing steps per (group, layout) try
WINDOW = 8          # candidates (a, N) tried per pass, lowest total first
INIT_BUDGET = 0.5   # seconds per candidate in the first pass
GROWTH = 1.5        # budget multiplier after a failed pass
MAX_A = 6           # maximum number of vertex blocks per side


# ----------------------------------------------------------------------------
# Baseline families (fast, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Block-voltage search over semidirect products Z_m x|_r Z_k of order N.
#
# Vertices: A_i(x) and B_j(y) for blocks i, j in range(a) and group elements x, y.
# Dart (i, j, g) gives edges A_i(x) -- B_j(x*g) for all x. Left multiplication
# by any group element is an automorphism, so eccentricities need only be
# checked from A_i(e) and B_j(e), one source per block.
# Each A-block has exactly d darts and each B-block receives exactly d darts,
# built from d random permutations of the blocks, so the graph is d-regular
# and bipartite. Total order is 2 * a * N.
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


def _tables(N, m, k, r, cache):
    """Return (multiplication table, inverse list) for the group, cached by parameters."""
    key = (m, k, r)
    if key not in cache:
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        cache[key] = (T, invs)
    return cache[key]


def _unreached(a, N, T, invs, darts, D):
    """Count (source, vertex) pairs not within distance D, for the 2a block sources at identity."""
    V = 2 * a * N
    out = [[] for _ in range(a)]
    inc = [[] for _ in range(a)]
    for i, j, g in darts:
        out[i].append((j, g))
        inc[j].append((i, invs[g]))
    total = 0
    for s in range(2 * a):
        src = s * N                      # element e of block s
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                b, x = divmod(u, N)
                row = T[x]
                if b < a:
                    for j, g in out[b]:
                        v = (a + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for i, hi in inc[b - a]:
                        v = i * N + row[hi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _random_darts(a, N, d, rng):
    """Random base layout: d permutation layers of a blocks, each dart with a distinct element per (i, j)."""
    pairs = []
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            pairs.append((i, perm[i]))
    darts = []
    for i, j in pairs:
        used = {g for (i2, j2, g) in darts if i2 == i and j2 == j}
        while True:
            g = rng.randrange(N)
            if g not in used:
                break
        darts.append((i, j, g))
    return darts


def _anneal(a, N, T, invs, darts, D, rng, iters, deadline):
    """Simulated annealing over the dart group elements to zero unreached pairs."""
    cur = _unreached(a, N, T, invs, darts, D)
    L = len(darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        k = rng.randrange(L)
        i, j, _ = darts[k]
        c = rng.randrange(N)
        clash = any(q != k and darts[q][0] == i and darts[q][1] == j and darts[q][2] == c
                    for q in range(L))
        if clash:
            continue
        nd = darts[:]
        nd[k] = (i, j, c)
        v = _unreached(a, N, T, invs, nd, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = nd, v
    return darts if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline, cache):
    """Try groups of order N with a blocks per side until one yields a valid layout, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, k, r, cache)
        darts = _random_darts(a, N, d, rng)
        res = _anneal(a, N, T, invs, darts, D, rng, ITERS, deadline)
        if res is not None:
            return res, T
    return None


def _candidates(d, moore, best_n):
    """Pairs (total, a, N) with total = 2*a*N above best_n and within the Moore bound, lowest first."""
    cands = []
    for a in range(1, MAX_A + 1):
        lo = max(d, best_n // (2 * a) + 1)
        hi = moore // (2 * a)
        for N in range(lo, hi + 1):
            cands.append((2 * a * N, a, N))
    cands.sort()
    return cands[:WINDOW]


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
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
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

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    budget = INIT_BUDGET
    cache = {}

    while time.monotonic() < deadline:
        cands = _candidates(d, moore, best_n)
        if not cands:
            break
        success = False
        for total, a, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget), cache)
            if res is None:
                continue
            (darts, T), _ = res, None
            edges = []
            for i, j, g in darts:
                for x in range(N):
                    edges.append((i * N + x, (a + j) * N + T[x][g]))
            if consider(2 * a * N, edges):
                success = True
                break
        if not success:
            budget *= GROWTH

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
