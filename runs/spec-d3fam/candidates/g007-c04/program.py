import math
import random
import time

import lib

TIME_FRAC = 0.80        # fraction of time_limit used before returning
MARGIN = 3.0            # seconds kept in reserve
BASE_STEPS = 3000       # annealing steps for the first pass (doubles each pass)
GROUPS_PER_N = 12       # candidate groups tried per order per pass
CACHE_LIMIT = 40        # max cached group tables before the cache is cleared


# ---------------------------------------------------------------- Cayley search
#
# Bipartite Cayley graph on two copies of a group G of order N:
#   a_g ~ b_h  iff  g^-1 h in S,  |S| = d.
# Every vertex has degree d. Vertices a_x, a_y are at distance <= 2 iff
# x^-1 y lies in S S^-1, and b-vertices behave the same way. Hence if
# S S^-1 = G, every pair is within distance 3. Then n = 2N, and the bound
# N <= d^2 - d + 1 is the Moore-type limit for this family.

_cache = {}


def _group_candidates(N, rng):
    """Semidirect groups Z_m x| Z_k (order N) given as (m, k, r) triples."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:GROUPS_PER_N]


def _group_tables(m, k, r):
    key = (m, k, r)
    if key in _cache:
        return _cache[key]
    if len(_cache) >= CACHE_LIMIT:
        _cache.clear()
    order, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    _cache[key] = (order, M, I)
    return _cache[key]


def _search(N, M, I, d, rng, steps, deadline):
    """Simulated annealing for S (|S| = d) with S S^-1 = G. Returns S or None."""
    if N <= d:
        return None
    cnt = [0] * N
    inS = [False] * N
    zeros = [N]
    S = []

    def inc(g):
        if cnt[g] == 0:
            zeros[0] -= 1
        cnt[g] += 1

    def dec(g):
        cnt[g] -= 1
        if cnt[g] == 0:
            zeros[0] += 1

    def add(y):
        inc(0)  # y y^-1 = identity
        for t in S:
            inc(M[y][I[t]])
            inc(M[t][I[y]])
        S.append(y)
        inS[y] = True

    def rem(x):
        S.remove(x)
        inS[x] = False
        for t in S:
            dec(M[x][I[t]])
            dec(M[t][I[x]])
        dec(0)

    init = rng.sample(range(N), d)
    for y in init:
        add(y)

    for step in range(steps):
        if (step & 255) == 0 and time.monotonic() > deadline:
            break
        if zeros[0] == 0:
            break
        T = 0.6 * (1.0 - step / steps) + 0.02
        x = S[rng.randrange(d)]
        y = rng.randrange(N)
        while inS[y]:
            y = rng.randrange(N)
        old = zeros[0]
        rem(x)
        add(y)
        delta = zeros[0] - old
        if delta > 0 and rng.random() >= math.exp(-delta / T):
            rem(y)
            add(x)

    return list(S) if zeros[0] == 0 else None


def _cayley_search(d, rng, deadline, lo, top):
    """Look for a Cayley construction with group order N in [lo, top]. Returns (n, edges) or None."""
    best = None
    floor = lo - 1           # only orders above floor are still of interest
    groups = {}
    passes = 0
    while time.monotonic() < deadline and top > floor:
        steps = BASE_STEPS * (1 << min(passes, 12))
        passes += 1
        for N in range(top, floor, -1):
            if time.monotonic() >= deadline:
                break
            if N not in groups:
                groups[N] = _group_candidates(N, rng)
            found = None
            for (m, k, r) in groups[N]:
                if time.monotonic() >= deadline:
                    break
                order, M, I = _group_tables(m, k, r)
                S = _search(order, M, I, d, rng, steps, deadline)
                if S is not None:
                    edges = [(g, order + M[g][s]) for g in range(order) for s in S]
                    found = (2 * order, edges)
                    break
            if found is not None:
                best = found
                floor = N   # later passes only look for strictly larger orders
                break
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every case.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    try:
        # Known constructions as baselines (validated).
        if D == 3:
            bases = []
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                try:
                    bases.append(lib.araujo_lopez_graph(d - 2))
                except Exception:
                    pass
            q = d - 1
            while q >= 2 and not lib.is_prime_power(q):
                q -= 1
            if q >= 2:
                bases.append(lib.projective_plane_incidence(q))
            for n, e in bases:
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e

            # New construction: Cayley bipartite graphs with a difference cover.
            top = d * d - d + 1
            lo = best_n // 2 + 1
            if top >= lo:
                cay = _cayley_search(d, rng, deadline, lo, top)
                if cay is not None and cay[0] > best_n:
                    n, e = cay
                    if lib.is_valid(n, e, d, D):
                        best_n, best_e = n, e
    except Exception:
        pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return lib.haar_graph(d, range(d))
