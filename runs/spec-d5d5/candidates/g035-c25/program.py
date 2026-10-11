import math
import random
import time

import lib


MAX_GROUPS = 4        # groups tried per order N in the bi-Cayley seed sweep
CLIMB_ITERS = 150     # hill-climb steps per group
ANNEAL_ITERS = 1500   # 2-switch annealing steps per repair round
ANNEAL_ROUNDS = 3     # repair rounds per grown graph before giving up
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baseline: projective plane incidence graphs (D = 3).
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q <= 60)."""
    for q in range(min(d - 1, 60), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Seed: bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
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
    """Cached (order, mul, T, invs) for the semidirect product, with T[x][g] = x*g."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, target) at distance > D, sources A_0 and B_0 (left translations are automorphisms)."""
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
    """Hill-climb a connection set S (containing 0) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
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
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_seed(d, D, rng, deadline):
    """Sweep N upward; return (n, edges) of the largest valid d-regular bi-Cayley lift found."""
    best = None
    N = d
    while time.monotonic() < deadline:
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
            best = (2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        N += 1
    return best


# ----------------------------------------------------------------------------
# Main construction: grow by vertex insertion, repair by 2-switch annealing.
#
# State: adj (adjacency lists over labels 0..n-1) and E (list of (a, b) pairs,
# a on the "A" side, b on the "B" side). The graph is d-regular and bipartite.
#
# Insertion: pick d disjoint edges (x_i, y_i). Add new A-vertex a adjacent to
# all y_i and new B-vertex b adjacent to all x_i. Every degree is restored,
# so the graph stays d-regular and bipartite. Bad pairs (distance > D) are then
# removed by degree-preserving 2-switches, accepted by simulated annealing.
# ----------------------------------------------------------------------------

def _add_edge(adj, a, b):
    adj[a].append(b)
    adj[b].append(a)


def _rem_edge(adj, a, b):
    adj[a].remove(b)
    adj[b].remove(a)


def _bad(adj, D):
    """Number of unordered vertex pairs at distance > D."""
    n = len(adj)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return (n * n - sum(x.bit_count() for x in ball)) // 2


def _anneal(adj, E, D, rng, deadline, iters):
    """Degree-preserving 2-switch annealing on bad-pair count. Returns the final cost."""
    cost = _bad(adj, D)
    if cost == 0 or len(E) < 2:
        return cost
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        _rem_edge(adj, a1, b1)
        _rem_edge(adj, a2, b2)
        _add_edge(adj, a1, b2)
        _add_edge(adj, a2, b1)
        c2 = _bad(adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            _rem_edge(adj, a1, b2)
            _rem_edge(adj, a2, b1)
            _add_edge(adj, a1, b1)
            _add_edge(adj, a2, b2)
    return cost


def _grow(adj, E, d, rng):
    """Insert one A-vertex and one B-vertex, keeping d-regularity. Returns None if no d-matching is found."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, pick = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    na = len(adj)
    nb = na + 1
    adj.append([])
    adj.append([])
    for i in pick:
        a, b = E[i]
        _rem_edge(adj, a, b)
        E[i] = (na, b)
        _add_edge(adj, na, b)
        E.append((a, nb))
        _add_edge(adj, a, nb)
    return adj, E


def _evolve(adj, E, d, D, rng, deadline):
    """Repeatedly grow the current valid graph and repair it; keep the last valid one."""
    best_adj, best_E = adj, E
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        cadj = [list(x) for x in best_adj]
        cE = list(best_E)
        g = _grow(cadj, cE, d, rng)
        if g is None:
            fails += 1
            continue
        cadj, cE = g
        cost = None
        for _ in range(ANNEAL_ROUNDS):
            cost = _anneal(cadj, cE, D, rng, deadline, ANNEAL_ITERS)
            if cost == 0 or time.monotonic() >= deadline:
                break
        if cost == 0:
            best_adj, best_E = cadj, cE
            fails = 0
        else:
            fails += 1
    return best_adj, best_E


def _from_edges(n, edges):
    adj = [[] for _ in range(n)]
    E = []
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        E.append((u, v))
    return adj, E


def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


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

    # Safe fallback: K_{d,d} is d-regular with diameter 2.
    fallback = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2:
        return fallback

    moore = lib._moore_bound(d, D)
    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = _pg_baseline(d) if D == 3 else None
    if pg is not None:
        consider(pg[0], pg[1])
    if best[0] >= moore:
        return best

    # Regular starting graphs for the grow-and-repair phase.
    starts = [fallback]
    bc = _bicayley_seed(d, D, rng, start + 0.3 * budget)
    if bc is not None:
        consider(bc[0], bc[1])
        starts.append(bc)
    if pg is not None:
        starts.append(pg)
    regular = [s for s in starts if _is_regular(s[0], s[1], d)]
    n0, e0 = max(regular, key=lambda s: s[0])

    adj, E = _from_edges(n0, e0)
    adj, E = _evolve(adj, E, d, D, rng, deadline)
    n2 = len(adj)
    consider(n2, [(a, b) for a, b in E])

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
