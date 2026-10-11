import math
import random
import time

import lib


_BIG = 10 ** 9
_RCACHE = {}


# ----------------------------------------------------------------------------
# Group sampling: semidirect products Z_m x| Z_k2 (order G), with cyclic fallback.
# ----------------------------------------------------------------------------

def _valid_r(m, k2):
    """All r in [1, m) with gcd(r, m) = 1 and r^k2 = 1 mod m (cached)."""
    key = (m, k2)
    if key not in _RCACHE:
        _RCACHE[key] = [r for r in range(1, m)
                        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    return _RCACHE[key]


def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G, preferring non-abelian ones."""
    pairs = [(m, G // m) for m in range(2, G) if G % m == 0]
    rng.shuffle(pairs)
    for m, k2 in pairs:
        if k2 < 2:
            continue
        rs = _valid_r(m, k2)
        nonab = [r for r in rs if r != 1]
        if nonab and rng.random() < 0.8:
            r = rng.choice(nonab)
        elif rs:
            r = rng.choice(rs)
        else:
            continue
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    order, mul, _ = lib.cyclic_group(G)
    return order, mul


def _rperm(cache, mul, G, s):
    """Cached permutation g -> mul(g, s)."""
    p = cache.get(s)
    if p is None:
        p = [mul(g, s) for g in range(G)]
        cache[s] = p
    return p


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts with k base vertices per side and d layers.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Each layer is a permutation
# of the k base vertices, so all degrees equal d.
# Left multiplication is an automorphism, so BFS from the k A-reps and the
# k B-reps decides validity exactly.
# ----------------------------------------------------------------------------

def _rep_cost(N, adj, reps, D, limit):
    """Total number of vertices not reached within D from the representatives."""
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
        if total > limit:
            return total
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    cache = {}
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def evaluate(limit):
        if len({(a, b, c) for a, b, c in darts}) < len(darts):
            return _BIG
        adj = [[] for _ in range(N)]
        for i, j, s in darts:
            pm = _rperm(cache, mul, G, s)
            ba = i * G
            bb = (k + j) * G
            for g in range(G):
                a = ba + g
                b = bb + pm[g]
                adj[a].append(b)
                adj[b].append(a)
        return _rep_cost(N, adj, reps, D, limit)

    cost = evaluate(float("inf"))
    T0, Tend = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (Tend / T0) ** (it / iters)
        limit = cost - T * math.log(1.0 - rng.random())  # Metropolis threshold

        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = evaluate(limit)
            if c2 < _BIG and c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = evaluate(limit)
            if c2 < _BIG and c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost != 0:
        return None
    E = []
    for i, j, s in darts:
        pm = _rperm(cache, mul, G, s)
        for g in range(G):
            E.append((i * G + g, (k + j) * G + pm[g]))
    return N, E


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 2: the even cycle C_{2D} is optimal.
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Projective plane baseline (diameter 3) with the largest prime power q <= d - 1.
    if D >= 3:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
        if best_n >= moore:
            return best

    # Voltage-lift portfolio, aimed at orders above the current best.
    ks = [1, 2, 3, 4, 6] if D >= 5 else [1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        gmin = best_n // (2 * k) + 1          # smallest G with 2kG > best_n
        G = gmin + rng.choice([0, 0, 0, 1, 1, 2, 3])
        if G < 2:
            continue
        order, mul = _sample_group(G, rng)
        slice_end = min(deadline, time.monotonic() + 6.0)
        res = _anneal(d, D, k, order, mul, rng, slice_end, iters=2500)
        if res is not None:
            consider(res[0], res[1])
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
