import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12       # groups tried per bi-Cayley order N in one pass
ATTEMPT_ITERS = 220   # tabu steps before a random restart of the connection set
SAMPLE = 40           # candidate moves evaluated per tabu step
TENURE = 9            # steps a vacated (slot, value) pair stays forbidden
STALL_LIMIT = 80      # steps without improvement before restarting
SLICE = 6.0           # seconds spent on one order N before moving to the next
WINDOW = 14           # bi-Cayley orders considered above the current lower bound

_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline for D = 3: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k, connection set found by tabu search.
#
# Vertices A_x = x and B_y = N + y for x, y in G, |G| = N.
# Edges A_x -- B_{x s} for s in S, |S| = d, identity WLOG in S.
# Left multiplication is an automorphism, so the eccentricities of A_0 and B_0
# decide the diameter. The count of unreached pairs is the search objective.
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
    """Cached (order, mul, T, invs): T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    if key in _CACHE:
        return _CACHE[key]
    if len(_CACHE) > 8:
        _CACHE.clear()
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    _CACHE[key] = (order, mul, T, invs)
    return _CACHE[key]


def _unreached(N, T, invs, S, D):
    """Number of (source, target) pairs at distance > D, sources A_0 and B_0."""
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


def _tabu(N, T, invs, d, D, rng, deadline):
    """Tabu search over connection sets with random restarts; returns S with zero cost or None."""
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _unreached(N, T, invs, S, D)
        best_cost = cur
        tabu = {}
        stall = 0
        for it in range(ATTEMPT_ITERS):
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            move = None
            mcost = None
            for _ in range(SAMPLE):
                i = rng.randrange(1, d)
                c = rng.randrange(1, N)
                if c in S:
                    continue
                S2 = S[:]
                old = S2[i]
                S2[i] = c
                v = _unreached(N, T, invs, S2, D)
                if tabu.get((i, c), -1) > it and v >= best_cost:
                    continue
                if mcost is None or v < mcost:
                    move = (i, old, S2)
                    mcost = v
            if move is None:
                continue
            i, old, S = move
            tabu[(i, old)] = it + TENURE
            cur = mcost
            if cur == 0:
                return S
            if cur < best_cost:
                best_cost = cur
                stall = 0
            else:
                stall += 1
                if stall > STALL_LIMIT:
                    break
    return None


def _search_order(N, d, D, rng, deadline):
    """Try groups of order N in turn, sharing the time left until deadline; return (T, S) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    groups = groups[:MAX_GROUPS]
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        gd = now + (deadline - now) / (len(groups) - idx)
        _, _, T, invs = _tables(m, k, r)
        S = _tabu(N, T, invs, d, D, rng, gd)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

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
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        # Cycle C_{2D} has diameter D and meets the Moore bound.
        consider(*lib.haar_graph(D, [0, 1]))
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts aiming strictly above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        cur_lo = best[0] // 2 + 1
        hi = min(cur_lo + WINDOW, moore // 2)
        if cur_lo > hi:
            break
        progressed = False
        for N in range(cur_lo, hi + 1):
            if time.monotonic() >= deadline:
                break
            if best[0] >= 2 * N:
                continue
            od = min(deadline, time.monotonic() + SLICE)
            found = _search_order(N, d, D, rng, od)
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                progressed = True
        if not progressed and time.monotonic() >= deadline:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
