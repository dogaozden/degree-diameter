import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Safe baseline: incidence graph of PG(2, q) with q the largest prime power <= d-1.
# It is valid for any D >= 3 and gives a strong fallback for small d.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_kk.
#
# k base vertices per side. The graph has 2*k*G vertices, A_{i,g} = i*G+g and
# B_{j,h} = (k+j)*G+h. A layer is a permutation perm of range(k) plus one voltage
# sv[i] per base vertex i, giving edges A_{i,g} -- B_{perm[i], g*sv[i]}.
# Every layer adds one edge-set per base vertex, so degree = number of layers.
# Left multiplication is an automorphism, so only one BFS per base vertex is needed.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, kk, r) with m*kk = G, m >= 2, giving the semidirect product Z_m x| Z_kk."""
    out = []
    for kk in range(1, G + 1):
        if G % kk:
            continue
        m = G // kk
        if m < 2:
            continue
        if kk == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


class _Group:
    """Caches right-multiplication permutations g -> g*s."""

    def __init__(self, order, mul):
        self.G = order
        self.mul = mul
        self.cache = {}

    def perm(self, s):
        p = self.cache.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self.cache[s] = p
        return p


def _cost(k, G, D, layers, grp, limit=float("inf")):
    """Number of (base representative, vertex) pairs not reached within D. Zero means valid."""
    seen_keys = set()
    darts = []
    for perm, sv in layers:
        for i in range(k):
            key = (i, perm[i], sv[i])
            if key in seen_keys:
                return _BIG          # duplicate edge set
            seen_keys.add(key)
            darts.append(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        p = grp.perm(s)
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + p[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        reached = bytearray(N)
        reached[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not reached[v]:
                        reached[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _anneal(d, D, k, G, grp, rng, deadline):
    """Anneal voltages and layer permutations. Returns the layers if cost reaches 0, else None."""
    layers = [[rng.sample(range(k), k), [rng.randrange(G) for _ in range(k)]]
              for _ in range(d)]
    cost = _cost(k, G, D, layers, grp)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.03, T * 0.999)
        limit = cost - T * math.log(1.0 - rng.random())
        new = [[list(p), list(s)] for p, s in layers]
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            new[L][1][i] = rng.randrange(G)
        else:
            a, b = rng.sample(range(k), 2)
            p = new[L][0]
            p[a], p[b] = p[b], p[a]
        c2 = _cost(k, G, D, new, grp, limit)
        if c2 <= limit:
            layers, cost = new, c2
    return layers if cost == 0 else None


def _edges(k, G, layers, grp):
    E = set()
    for perm, sv in layers:
        for i in range(k):
            j = perm[i]
            p = grp.perm(sv[i])
            for g in range(G):
                E.add((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main new search: bi-Cayley lifts over non-abelian semidirect products.
    if D >= 3 and d >= 3:
        ks = [1, 1, 1, 2, 2, 3]
        while time.monotonic() < deadline and best_n < moore:
            k = rng.choice(ks)
            lo = max(2, best_n // (2 * k) + 1, int(0.42 * moore / (2 * k)))
            hi = lo + max(4, lo // 8)
            G = rng.randint(lo, hi)
            groups = _groups_of_order(G)
            if not groups:
                continue
            nonab = [g for g in groups if g[1] > 1]
            pool = nonab if (nonab and rng.random() < 0.85) else groups
            m, kk, r = rng.choice(pool)
            try:
                order, mul, _ = lib.semidirect_group(m, kk, r)
            except ValueError:
                continue
            grp = _Group(order, mul)
            slice_end = min(deadline, time.monotonic() + 6.0)
            layers = _anneal(d, D, k, order, grp, rng, slice_end)
            if layers is not None:
                n, e = _edges(k, order, layers, grp)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
