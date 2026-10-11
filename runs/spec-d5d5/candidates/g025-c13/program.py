import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Structured baseline for D = 3: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with annealed connection sets.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
_BIG = 10 ** 9
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
    """Cached (order, mul, T, invs) for the semidirect group; T[x][g] = x*g."""
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
    """Unreached (source, target) pairs from A_0 and B_0 in the Bi-Cayley graph A_x ~ B_{x g}."""
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
    """Annealed search for a connection set S of size d with zero unreached pairs; None on failure."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


def _bicayley_try(d, D, N, rng, deadline):
    """Try a few groups of order N; return (2N, edges) for a valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            return 2 * N, edges
    return None


# ----------------------------------------------------------------------------
# Bold new family: direct annealing over d-regular bipartite graphs.
# Degree-preserving edge swaps keep the graph bipartite and d-regular; the
# cost is the number of vertex pairs at distance > D. This is not a lift.
# ----------------------------------------------------------------------------

def _cost_pairs(n, E, D):
    """Number of unordered vertex pairs at distance more than D."""
    nb = [[] for _ in range(n)]
    for a, b in E:
        nb[a].append(b)
        nb[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _random_biregular(h, d, rng):
    """Union of d random perfect matchings between sides of size h, with no repeated edges."""
    eset = set()
    E = []
    for _ in range(d):
        found = False
        for _ in range(400):
            p = list(range(h))
            rng.shuffle(p)
            if all((a, h + p[a]) not in eset for a in range(h)):
                found = True
                break
        if not found:
            return None
        for a in range(h):
            e = (a, h + p[a])
            eset.add(e)
            E.append(e)
    return E, eset


def _swap_anneal(h, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on 2h vertices to diameter D; return (2h, edges) or None."""
    init = _random_biregular(h, d, rng)
    if init is None:
        return None
    E, eset = init
    n = 2 * h
    cur = _cost_pairs(n, E, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 2.0, 0.15
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1 = (a, e)
        f2 = (c, b)
        if f1 in eset or f2 in eset:
            continue
        E[i] = f1
        E[j] = f2
        new = _cost_pairs(n, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add(f1)
            eset.add(f2)
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    if cur == 0:
        return n, list(E)
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
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

    if best[0] < moore and d >= 2:
        # Phase 1: Bi-Cayley lifts, a modest share of the budget.
        bc_deadline = start + 0.3 * budget
        while best[0] < moore and time.monotonic() < bc_deadline:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            N = lo + rng.randrange(max(1, lo // 20))
            res = _bicayley_try(d, D, N, rng, bc_deadline)
            if res is not None:
                consider(*res)

        # Phase 2: direct swap annealing on d-regular bipartite graphs,
        # aiming one side larger than the current best.
        while best[0] < moore and time.monotonic() < deadline:
            h = best[0] // 2 + 1
            if 2 * h > moore or h < d:
                break
            res = _swap_anneal(h, d, D, rng, deadline)
            if res is None:
                break
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
