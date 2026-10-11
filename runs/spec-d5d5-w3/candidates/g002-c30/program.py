import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

SA_FRACTION = 0.55      # share of the budget given to the new annealing search (d=5, D=5)
SA_START_N = 169        # 2*169 = 338 > record 336
SA_T0 = 6.0
SA_T1 = 0.3
MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
N_WINDOW = 8

_TCACHE = {}


# ----------------------------------------------------------------------------
# New construction: annealed bipartite d-regular graphs (edge switches).
# Start from a Haar graph on Z_N (simple, d-regular, bipartite), then apply
# degree-preserving switches (a,b),(a2,b2) -> (a,b2),(a2,b) and accept by
# simulated annealing on the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(adj, n, D):
    """Number of unordered vertex pairs at distance > D, via bitset ball growth."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _haar_adj(N, S):
    """Adjacency lists of the Haar graph: A_a ~ B_{a+s} for s in S (global ids, B = N..2N-1)."""
    adj = [[] for _ in range(2 * N)]
    for a in range(N):
        for s in S:
            b = N + (a + s) % N
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _rewire(adj, adjs, rem, add):
    """Remove the edges in rem and add the edges in add, keeping lists and sets in sync."""
    for u, v in rem:
        adj[u].remove(v)
        adj[v].remove(u)
        adjs[u].discard(v)
        adjs[v].discard(u)
    for u, v in add:
        adj[u].append(v)
        adj[v].append(u)
        adjs[u].add(v)
        adjs[v].add(u)


def _anneal(d, D, N, rng, deadline):
    """Anneal a d-regular bipartite graph on 2N vertices toward diameter D; return edges or None."""
    n = 2 * N
    adj = _haar_adj(N, rng.sample(range(N), d))
    adjs = [set(x) for x in adj]
    cost = _bad(adj, n, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    frac = 0.0
    it = 0
    while cost > 0:
        it += 1
        if it & 15 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = min(1.0, (now - t0) / span)
        T = SA_T0 * (SA_T1 / SA_T0) ** frac

        a = rng.randrange(N)
        b = adj[a][rng.randrange(d)]
        a2 = rng.randrange(N)
        if a2 == a:
            continue
        b2 = adj[a2][rng.randrange(d)]
        if b2 == b or b2 in adjs[a] or b in adjs[a2]:
            continue

        _rewire(adj, adjs, [(a, b), (a2, b2)], [(a, b2), (a2, b)])
        c2 = _bad(adj, n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _rewire(adj, adjs, [(a, b2), (a2, b)], [(a, b), (a2, b2)])

    return [(a, b) for a in range(N) for b in adj[a]]


# ----------------------------------------------------------------------------
# Fallback: bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# ----------------------------------------------------------------------------

def _groups(N):
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
    hit = _TCACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TCACHE) >= 48:
        _TCACHE.clear()
    _TCACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, cap=None):
    """Count (source, vertex) pairs not within distance D for sources A_0 and B_0."""
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
        if cap is not None and total > cap:
            return total
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
        v = _unreached(N, T, invs, S2, D, cap=cur)
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


def _bicayley(d, D, N, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 3, D = 3: PG(2,2) incidence graph, 14 vertices, diameter 3.
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        if lib.is_valid(best[0], best[1], d, D):
            return best

    try:
        # New search for d = 5, D = 5: annealed bipartite graphs above the record order.
        if d == 5 and D == 5:
            sa_deadline = start + SA_FRACTION * budget
            N = SA_START_N
            while time.monotonic() < sa_deadline:
                edges = _anneal(d, D, N, rng, sa_deadline)
                if edges is None:
                    break
                consider(2 * N, edges)
                N += 1

        # Fallback / remaining time: bi-Cayley lifts that beat the current best order.
        moore = lib.moore_bound(d, D)
        while best_n < moore and time.monotonic() < deadline:
            lo = best_n // 2 + 1
            if lo > moore // 2:
                break
            N = lo + rng.randrange(N_WINDOW)
            if N <= d:
                continue
            res = _bicayley(d, D, N, rng, deadline)
            if res is not None:
                T, S = res
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
