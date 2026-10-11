import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over semidirect products Z_m x|_r Z_k.
#
# A base graph has k "A" orbits and k "B" orbits. Each of the d layers is a
# permutation p_l of range(k) together with voltages s_{l,i} in the group G.
# A_{i,x} is joined to B_{p_l(i), x*s_{l,i}} for every layer l. Every vertex
# then has degree d, the graph is bipartite, and left translation by G is an
# automorphism. Simulated annealing over voltages and layer permutations
# minimises the number of vertex pairs farther apart than D, measured from one
# representative per orbit. Sweeping the group order upward finds valid graphs
# above the current best order. This differs from the single-orbit hill climb
# used by the parent.
# ----------------------------------------------------------------------------

BIG = 10 ** 9
ATTEMPT_SECS = 4.0
ANNEAL_ITERS = 2500
_TABLE_CACHE = {}
_GROUPS_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    hit = _GROUPS_CACHE.get(N)
    if hit is not None:
        return hit
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUPS_CACHE[N] = out
    return out


def _group_table(m, k, r):
    """T[x][g] = x*g for the semidirect product Z_m x|_r Z_k (cached)."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    if len(_TABLE_CACHE) > 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = T
    return T


def _dup_free(k, perms, vol, d):
    """True if no two darts share the same (i, j, voltage) triple."""
    seen = set()
    for l in range(d):
        p = perms[l]
        v = vol[l]
        for i in range(k):
            key = (i, p[i], v[i])
            if key in seen:
                return False
            seen.add(key)
    return True


def _adj(k, G, T, perms, vol, d):
    """Adjacency lists of the lift. Orbit A_i is index i*G + x, orbit B_j is (k+j)*G + y."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for l in range(d):
        p = perms[l]
        v = vol[l]
        for i in range(k):
            base_a = i * G
            base_b = (k + p[i]) * G
            s = v[i]
            for x in range(G):
                a = base_a + x
                b = base_b + T[x][s]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _unreached(adj, N, reps, D):
    """Total number of (representative, vertex) pairs not reached within distance D."""
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, T, perms, vol, d):
    E = set()
    for l in range(d):
        p = perms[l]
        v = vol[l]
        for i in range(k):
            j = p[i]
            s = v[i]
            for x in range(G):
                E.add((i * G + x, (k + j) * G + T[x][s]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    perms = [rng.sample(range(k), k) for _ in range(d)]
    vol = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def cost_of():
        if not _dup_free(k, perms, vol, d):
            return BIG
        adj = _adj(k, G, T, perms, vol, d)
        return _unreached(adj, N, reps, D)

    cost = cost_of()
    t0 = max(2.0, 0.05 * cost) if cost < BIG else 2.0
    t_end = 0.3
    decay = (t_end / t0) ** (1.0 / max(1, iters)) if t0 > t_end else 1.0
    temp = t0

    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(t_end, temp * decay)
        l = rng.randrange(d)
        if k == 1 or rng.random() < 0.8:
            i = rng.randrange(k)
            old = vol[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            vol[l][i] = new
            c2 = cost_of()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                vol[l][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            p = perms[l]
            p[a], p[b] = p[b], p[a]
            c2 = cost_of()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]

    if cost == 0:
        return _edges(k, G, T, perms, vol, d)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Structured baseline: projective plane incidence for D = 3, d - 1 a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n2, e2 = lib.projective_plane_incidence(d - 1)
        consider(n2, e2)

    # Main search: multi-orbit lifts, sweeping group order upward.
    ks = (1, 1, 2, 2, 3)
    while best[0] < moore and time.monotonic() < deadline:
        k = rng.choice(ks)
        n_best = best[0]
        lo = n_best // (2 * k) + 1
        if 2 * k * lo > moore:
            continue
        G = lo + rng.randrange(3)
        groups = _groups(G)
        m, k2, r = rng.choice(groups)
        T = _group_table(m, k2, r)
        attempt_deadline = min(deadline, time.monotonic() + ATTEMPT_SECS)
        res = _anneal(d, D, k, G, T, rng, attempt_deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
