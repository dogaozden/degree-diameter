import math
import random
import time

import lib


MAX_GROUPS = 8
CLIMB_ITERS = 800
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph (meets Moore bound for d = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Phase 1: Bi-Cayley lifts over Z_m x|_r Z_k (baseline, from earlier search).
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
    """Count vertex pairs not within distance D, from A_0 and B_0 (Bi-Cayley graph)."""
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
    """Simulated annealing over a connection set S; returns S if fully valid, else None."""
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


def _bicayley_phase(d, D, moore, rng, deadline, get_n, consider):
    """Repeatedly try Bi-Cayley lifts just above the current best order."""
    while time.monotonic() < deadline and get_n() < moore:
        lo = get_n() // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(max(2, lo // 10))
        if N > moore // 2:
            N = lo
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, _, T, invs = _tables(m, k2, r)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])


# ----------------------------------------------------------------------------
# Phase 2 (new): unstructured edge-switch annealing on d-regular bipartite
# graphs. Start from a cyclic bi-Cayley graph on N + N vertices (simple and
# d-regular), then repeatedly swap endpoints of two edges, which preserves
# regularity and bipartiteness. Cost = number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitmask balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal_bip(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with N + N vertices; return edge list (a, b) or None."""
    n = 2 * N
    S = rng.sample(range(N), d)
    E = [(x, (x + s) % N) for x in range(N) for s in S]
    Eset = set(E)

    def cost_of(edge_list):
        adj = [[] for _ in range(n)]
        for a, b in edge_list:
            adj[a].append(N + b)
            adj[N + b].append(a)
        return _bad_pairs(n, adj, D)

    cost = cost_of(E)
    if cost == 0:
        return E
    T0 = max(1.0, 0.05 * cost)
    T1 = 0.1
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(T1, T0 * (1.0 - (now - t0) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in Eset or e2 in Eset:
            continue
        E[i] = e1
        E[j] = e2
        c2 = cost_of(E)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add(e1)
            Eset.add(e2)
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if cost == 0 else None


def _grow_phase(d, D, moore, rng, deadline, get_n, consider):
    """Grow the per-side size with annealing; double the step on success, halve on failure."""
    N = get_n() // 2
    inc = 1
    while time.monotonic() < deadline:
        target = N + inc
        if 2 * target > moore:
            target = moore // 2
            if target <= N:
                break
        now = time.monotonic()
        cap = min(deadline, now + max(3.0, 0.5 * (deadline - now)))
        E = _anneal_bip(target, d, D, rng, cap)
        if E is not None:
            consider(2 * target, [(a, target + b) for a, b in E])
            N = target
            inc *= 2
        else:
            if inc == 1:
                break
            inc //= 2
    return N


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    def get_n():
        return best[0]

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best[0] < moore:
        _bicayley_phase(d, D, moore, rng, start + 0.35 * budget, get_n, consider)

    if best[0] < moore:
        _grow_phase(d, D, moore, rng, deadline, get_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
