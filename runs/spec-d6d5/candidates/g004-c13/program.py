"""Bi-Cayley voltage-lift search with a tabu-annealed objective, plus safe fallbacks.

Design (this variant):
- Safe fallback first: K_{d,d} (diameter 2), upgraded to the PG(2,q) incidence graph
  for D >= 3 when that is valid. Every candidate passes lib.is_valid before it is kept.
- Main family for D >= 4: bi-Cayley lifts over semidirect products Z_m x| Z_k2 with
  k base vertices per side. Each of the d layers is a perfect matching between the
  base sides, so every vertex has degree exactly d.
- Objective: number of (base representative, vertex) pairs farther than D apart.
  Group left-translation is an automorphism that acts transitively on each side, so
  only the 2k base representatives need BFS.
- Search moves: re-roll one voltage, or swap the B-targets of two darts in the same
  layer. Acceptance is Metropolis. An elite pool of low-cost failed states is
  perturbed and continued. The group-order window ratchets upward from the best
  valid order found so far.
"""
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe base constructions
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


# ----------------------------------------------------------------------------
# Lift representation and cost
# ----------------------------------------------------------------------------

def _perm_of(cache, mul, G, s):
    """Cached permutation g -> mul(g, s)."""
    p = cache.get(s)
    if p is None:
        p = [mul(g, s) for g in range(G)]
        cache[s] = p
    return p


def _build_adj(k, G, darts, cache, mul):
    """Adjacency lists of the lift. A(i,g) = i*G+g, B(j,h) = (k+j)*G+h."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = _perm_of(cache, mul, G, s)
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, G, D, adj, limit):
    """Unreached (representative, vertex) pairs within distance D. Early exit above limit."""
    N = len(adj)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _eval(k, G, D, darts, cache, mul, limit):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    adj = _build_adj(k, G, darts, cache, mul)
    return _cost(k, G, D, adj, limit)


def _edges(k, G, darts, cache, mul):
    E = set()
    for i, j, s in darts:
        pm = _perm_of(cache, mul, G, s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, k, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        if rng.random() < 0.5:
            out[idx][2] = rng.randrange(G)
        else:
            L = idx // k
            a, b = rng.sample(range(k), 2) if k >= 2 else (0, 0)
            if k >= 2:
                ia, ib = L * k + a, L * k + b
                out[ia][1], out[ib][1] = out[ib][1], out[ia][1]
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, init=None, T0=1.0):
    """Metropolis search over voltages and within-layer B-swaps.

    Returns (darts, cost, cache). cost == 0 means the lift is valid.
    """
    cache = {}
    darts = [list(x) for x in init] if init is not None else _random_darts(d, k, G, rng)
    cur = _eval(k, G, D, darts, cache, mul, float("inf"))
    T = T0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cur - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _eval(k, G, D, darts, cache, mul, limit)
            if c2 <= limit:
                cur = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _eval(k, G, D, darts, cache, mul, limit)
            if c2 <= limit:
                cur = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cur, cache


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and d >= 2:
        pool = []  # elite failed states: (cost, k, G, mul, darts)
        ks = [1, 1, 2, 2, 3]
        while time.monotonic() < deadline:
            if pool and rng.random() < 0.4:
                pool.sort(key=lambda x: x[0])
                _, k, G, mul, init = rng.choice(pool[:4])
                init = _perturb(init, k, G, rng, rng.randint(1, 3))
                T0, iters = 0.4, 700
            else:
                k = rng.choice(ks)
                lo = max(2, best_n // (2 * k) + 1)
                G = rng.randint(lo, int(lo * 1.25) + 2)
                g = _sample_group(G, rng)
                if g is None:
                    continue
                G, mul = g
                init, T0, iters = None, 1.0, 600

            darts, c, cache = _anneal(d, D, k, G, mul, rng, deadline, iters, init, T0)
            if c == 0:
                n, e = _edges(k, G, darts, cache, mul)
                consider(n, e)
                continue

            pool.append((c, k, G, mul, darts))
            if len(pool) > 10:
                pool.sort(key=lambda x: x[0])
                del pool[10:]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
