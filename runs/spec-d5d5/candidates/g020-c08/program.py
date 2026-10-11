import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured D = 3 baseline: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side), hill-climbed.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
N_WINDOW = 8
_TABLE_CACHE = {}


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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Unreached (source, target) pairs from A_0 and B_0 for the bi-Cayley graph A_x ~ B_{xg}, g in S."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

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
        v = _unreached(N, T, invs, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid bi-Cayley lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Different construction: general bipartite d-regular graphs on N + N vertices,
# annealed by edge switches (degree- and bipartition-preserving) to minimize
# the number of ordered pairs at distance > D. No group structure is imposed.
# ----------------------------------------------------------------------------

def _bitcost(N2, nbr, D):
    """Number of ordered vertex pairs at distance > D, via bitset ball growth."""
    reach = [1 << v for v in range(N2)]
    for _ in range(D):
        new = []
        for v in range(N2):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N2 - r.bit_count() for r in reach)


def _lift_cost(N, E, D):
    """Cost of the bipartite graph with parts 0..N-1 and N..2N-1, edges (a, N+b) for (a, b) in E."""
    nbr = [[] for _ in range(2 * N)]
    for a, b in E:
        nbr[a].append(N + b)
        nbr[N + b].append(a)
    return _bitcost(2 * N, nbr, D)


def _random_regular(N, d, rng):
    """Random d-regular bipartite graph as a list of (a, b) pairs, built from d disjoint perfect matchings."""
    for _ in range(50):
        edges = set()
        ok = True
        for _layer in range(d):
            placed = False
            for _ in range(300):
                perm = list(range(N))
                rng.shuffle(perm)
                if all((i, perm[i]) not in edges for i in range(N)):
                    for i in range(N):
                        edges.add((i, perm[i]))
                    placed = True
                    break
            if not placed:
                ok = False
                break
        if ok:
            return list(edges)
    return None


def _anneal_lift(N, d, D, rng, deadline):
    """Edge-switch simulated annealing on a random d-regular bipartite graph; returns E or None."""
    E = _random_regular(N, d, rng)
    if E is None:
        return None
    eset = set(E)
    cur = _lift_cost(N, E, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.2
    while cur > 0:
        now = time.monotonic()
        if now >= deadline or len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        new = _lift_cost(N, E, D)
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return E if cur == 0 else None


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

    # Main search: mix bi-Cayley hill-climbing with direct annealed bipartite lifts,
    # always aiming just above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        now = time.monotonic()
        if rng.random() < 0.7:
            N = lo + rng.randrange(N_WINDOW)
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        else:
            N = lo + rng.randrange(3)
            slice_end = min(deadline, now + max(2.0, 0.15 * (deadline - now)))
            E = _anneal_lift(N, d, D, rng, slice_end)
            if E is not None:
                consider(2 * N, [(a, N + b) for a, b in E])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
