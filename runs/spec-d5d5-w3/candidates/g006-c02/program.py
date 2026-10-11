import math
import random
import time

import lib


# Structured baseline: incidence graph of PG(2, q), which meets the Moore bound for D = 3.
def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# Group families for bi-Cayley lifts of order N: semidirect Z_m x|_r Z_k and
# abelian direct products Z_a x Z_b (the abelian family is new in this version).
MAX_GROUPS = 14
POOL = 30
CLIMB_ITERS = 800
WINDOW = 6
WALK_P = 0.02
_TABLE_CACHE = {}


def _specs(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("s", m, k, r))
    for a in range(1, N + 1):
        if N % a == 0:
            out.append(("a", a, N // a))
    return out


def _table(spec):
    hit = _TABLE_CACHE.get(spec)
    if hit is not None:
        return hit
    if spec[0] == "s":
        _, m, k, r = spec
        order, mul, inv = lib.semidirect_group(m, k, r)
    else:
        _, a, b = spec
        order = a * b

        def mul(x, y):
            return ((x // b + y // b) % a) * b + (x % b + y % b) % b

        def inv(x):
            return ((-(x // b)) % a) * b + (-(x % b)) % b
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[spec] = val
    return val


# Bi-Cayley graph: A_x ~ B_{x*g} for g in S. Counts pairs not within D of A_0 or B_0.
def _unreached(N, T, invs, S, D):
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


# Greedy construction: repeatedly add the element that most reduces unreached pairs.
def _greedy(N, T, invs, d, D, rng, deadline):
    S = [0]
    while len(S) < d:
        if time.monotonic() > deadline:
            return None
        cands = rng.sample(range(1, N), min(POOL, N - 1))
        best_c, best_v = None, None
        for c in cands:
            if c in S:
                continue
            v = _unreached(N, T, invs, S + [c], D)
            if best_v is None or v < best_v:
                best_c, best_v = c, v
        if best_c is None:
            return None
        S.append(best_c)
    return S


# Swap-based local search with occasional uphill moves.
def _climb(N, T, invs, d, D, S, rng, deadline, iters):
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < WALK_P:
            S, cur = S2, v
    return S if cur == 0 else None


def _search_order(d, D, N, rng, deadline):
    specs = _specs(N)
    rng.shuffle(specs)
    for spec in specs[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        order, T, invs = _table(spec)
        if order != N or d > N:
            continue
        S = _greedy(N, T, invs, d, D, rng, deadline)
        if S is None:
            continue
        S = _climb(N, T, invs, d, D, S, rng, deadline, CLIMB_ITERS)
        if S is not None:
            return T, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts with orders N sweeping just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(WINDOW)
        res = _search_order(d, D, N, rng, deadline)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
