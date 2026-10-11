import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 13), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: edge-switch local search over random d-regular bipartite graphs.
# Cost = number of ordered vertex pairs at distance > D, computed with
# bitset balls (Python big ints). Moves swap two edges (a,b),(c,e) -> (a,e),(c,b),
# which keeps the graph bipartite and d-regular.
# ----------------------------------------------------------------------------

def _ball_cost(n, adj, D):
    """Number of ordered pairs (u, v) with dist(u, v) > D; unreachable pairs count."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _random_biregular(N, d, rng):
    """Union of d random perfect matchings between sides [0,N) and [N,2N), no repeated edges."""
    for _ in range(50):
        E = []
        eset = set()
        ok = True
        for _r in range(d):
            perm = None
            for _t in range(3000):
                cand = list(range(N))
                rng.shuffle(cand)
                if all((a, N + cand[a]) not in eset for a in range(N)):
                    perm = cand
                    break
            if perm is None:
                ok = False
                break
            for a in range(N):
                e = (a, N + perm[a])
                eset.add(e)
                E.append(e)
        if ok:
            return E, eset
    return None


def _switch_search(d, D, N, rng, deadline):
    """Anneal edge switches on a random d-regular bipartite graph with 2N vertices.

    Returns (n, edges) with zero bad pairs, or None if the deadline passes first.
    """
    init = _random_biregular(N, d, rng)
    if init is None:
        return None
    E0, eset = init
    E = [[a, b] for a, b in E0]
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cur = _ball_cost(n, adj, D)
    m = len(E)
    t0, t1 = 2.0, 0.2
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)

    while cur > 0 and time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t_start) / span)
        T = t0 * (t1 / t0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        # apply switch
        adj[a].remove(b)
        adj[b].remove(a)
        adj[c].remove(e)
        adj[e].remove(c)
        adj[a].append(e)
        adj[e].append(a)
        adj[c].append(b)
        adj[b].append(c)
        new = _ball_cost(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            # undo
            adj[a].remove(e)
            adj[e].remove(a)
            adj[c].remove(b)
            adj[b].remove(c)
            adj[a].append(b)
            adj[b].append(a)
            adj[c].append(e)
            adj[e].append(c)

    if cur != 0:
        return None
    return n, [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (inherited from the parent search).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
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
    """Unreached pairs counted from A_0 and B_0 (left translations are automorphisms)."""
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
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
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

    if best[0] >= moore:
        return best

    # Phase 1 (new): edge-switch annealing, sweeping N upward.
    sw_deadline = start + 0.35 * budget
    N = best[0] // 2 + 1
    while best[0] < moore and time.monotonic() < sw_deadline and N <= moore // 2:
        res = _switch_search(d, D, N, rng, sw_deadline)
        if res is None:
            break
        consider(res[0], res[1])
        N = max(N + 1, N + N // 25)

    # Phase 2: Bi-Cayley lifts above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(8)
        res = _search_bicayley(d, D, N, rng, deadline)
        if res is not None:
            T, S = res
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
