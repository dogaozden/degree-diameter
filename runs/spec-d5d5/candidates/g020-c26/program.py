import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines: projective planes (D >= 3) and K_{d,d} (fallback).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with annealed connection sets (kept from
# the parent; a different search family runs beside it).
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 800
SWITCH_ITERS = 6000
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
    """Unreached (source, target) pairs from A_0 and B_0 in the bi-Cayley graph."""
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
    """Annealing over a bi-Cayley connection set; returns S if fully valid else None."""
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


# ----------------------------------------------------------------------------
# NEW FAMILY: edge-switching annealing on bipartite d-regular graphs.
# Start from a random d-regular bipartite graph on N + N vertices and apply
# degree-preserving 2-switches (a-b, c-e) -> (a-e, c-b), accepting by the number
# of ordered vertex pairs at distance > D (computed with big-int bitset balls).
# ----------------------------------------------------------------------------

def _random_bi_regular(N, d, rng):
    """Edge list of a simple d-regular bipartite graph (left 0..N-1, right 0..N-1), or None."""
    S = set()
    edges = []
    for _ in range(d):
        new = None
        for _attempt in range(300):
            perm = list(range(N))
            rng.shuffle(perm)
            cand = [(i, perm[i]) for i in range(N)]
            if all(e not in S for e in cand):
                new = cand
                break
        if new is None:
            return None
        for e in new:
            S.add(e)
        edges.extend(new)
    return edges


def _cost(n, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D, via bitset balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball)


def _switch_anneal(N, d, D, rng, deadline, iters):
    """Annealed edge switching; returns (2N, edges) with diameter <= D, or None."""
    E = _random_bi_regular(N, d, rng)
    if E is None:
        return None
    n = 2 * N
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(N + b)
        adj[N + b].add(a)
    # Re-index: right vertices become N + b in adj; store edges as (left, right-global).
    E = [(a, N + b) for a, b in E]
    S = set(E)
    m = len(E)
    cost = _cost(n, adj, D)
    T0 = max(2.0, 0.02 * cost)
    for step in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - step / iters) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in S or (c, b) in S:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new_cost = _cost(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard((a, b)); S.discard((c, e))
            S.add((a, e)); S.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
            cost = new_cost
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    if cost == 0:
        return n, [(a, b) for a, b in E]
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

    # Safe fallback: K_{d,d} has diameter 2 and is always valid.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bold change for D >= 4 (target d5D5): mostly edge-switching annealing,
    # with bi-Cayley lifts as the second family.
    bicayley_prob = 0.3 if D == 5 else 0.5

    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        slice_end = min(deadline, time.monotonic() + 10.0)

        if rng.random() < bicayley_prob:
            N = lo + rng.randrange(max(2, lo // 10))
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > slice_end:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, slice_end)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            N = lo + rng.randrange(2)
            res = _switch_anneal(N, d, D, rng, slice_end, SWITCH_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
