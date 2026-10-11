import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: bipartite, degree d, diameter 2 (valid for every D >= 2)."""
    if d < 1:
        return 1, []
    return lib.haar_graph(d, range(d))


def _pg_graph(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over groups Z_m x| Z_k2, searched by simulated annealing.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}.
# The graph has d layers. Layer L is a permutation of the B's: A_i is
# joined to B_{J[L*k+i]}, and every dart carries a voltage V[t] in the group.
# Each A_i and each B_j then has degree exactly d (before duplicate checks).
#
# Vertex A_{i,g} = i*G + g, vertex B_{j,h} = (k+j)*G + h.
# Dart t = (i, j, s) joins A_{i,g} to B_{j, g*s} for every g.
# Cost = number of ordered vertex pairs at distance > D (bitset BFS). 0 = valid.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random group Z_m x| Z_k2 of order G, or None."""
    ks = [k2 for k2 in range(1, min(G, 12) + 1) if G % k2 == 0 and G // k2 >= 2]
    if not ks:
        return None
    for _ in range(40):
        k2 = rng.choice(ks)
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.cyclic_group(m)
            return order, mul
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
            return order, mul
        except ValueError:
            continue
    return None


def _cost(k, G, D, J, V, perm):
    """Ordered pairs not within distance D, computed with big-int bitsets. Zero means valid."""
    N = 2 * k * G
    seen = set()
    adj = [[] for _ in range(N)]
    for t in range(len(J)):
        i = t % k
        j = J[t]
        s = V[t]
        key = (i, j, s)
        if key in seen:
            return _BIG
        seen.add(key)
        p = perm(s)
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + p[g]
            adj[a].append(b)
            adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(N - x.bit_count() for x in reach)


def _edges(k, G, J, V, perm):
    E = set()
    for t in range(len(J)):
        i = t % k
        j = J[t]
        p = perm(V[t])
        for g in range(G):
            E.add((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages and layer permutations. Returns ((n, edges) or None, cost)."""
    J = []
    for _ in range(d):
        J.extend(rng.sample(range(k), k))
    V = [rng.randrange(G) for _ in range(d * k)]

    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    cost = _cost(k, G, D, J, V, perm)
    T0 = 3.0
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, T0 * (1.0 - it / iters))
        if k >= 2 and rng.random() < 0.35:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ta, tb = L * k + a, L * k + b
            J[ta], J[tb] = J[tb], J[ta]
            c2 = _cost(k, G, D, J, V, perm)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                J[ta], J[tb] = J[tb], J[ta]
        else:
            t = rng.randrange(len(V))
            old = V[t]
            new = rng.randrange(G)
            if new == old:
                continue
            V[t] = new
            c2 = _cost(k, G, D, J, V, perm)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                V[t] = old
    if cost == 0:
        return _edges(k, G, J, V, perm), 0
    return None, cost


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    best_n, best_e = _fallback(d)
    if D == 2:
        if lib.is_valid(best_n, best_e, d, D):
            return best_n, best_e
        return 2, [(0, 1)] if d >= 1 else (1, [])

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    try:
        if D >= 3:
            pg = _pg_graph(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

        ks = [1, 2, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            lo = best_n // (2 * k) + 1
            hi = lo + max(4, lo // 10)
            G = rng.randint(max(2, lo), max(2, hi))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res, _ = _anneal(d, D, k, order, mul, rng, deadline, 1200)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = _fallback(d)
    return best_n, best_e
