import math
import random
import time
from math import gcd

import lib


# Bi-Cayley (Haar-type) search over groups of order G, with one base vertex per side.
# Vertices: a_g = g and b_x = G + x. Connection set S (|S| = d, identity in S WLOG)
# gives edges a_g -- b_{g*s} for s in S. Left multiplication is an automorphism
# that is transitive on each side, so diameter <= D reduces to two BFS runs,
# from a_identity and from b_identity.

class _Group:
    """Finite group of order G with cached right-multiplication columns."""

    def __init__(self, G, mul, inv):
        self.G = G
        self._mul = mul
        self._inv = inv
        self._cols = {}

    def col(self, s):
        c = self._cols.get(s)
        if c is None:
            mul = self._mul
            c = [mul(g, s) for g in range(self.G)]
            self._cols[s] = c
        return c

    def inv(self, s):
        return self._inv(s)


def _sample_group(G, rng):
    """Random group of order G: cyclic, or a semidirect product Z_m x| Z_k with small k."""
    ks = [k for k in range(2, 13) if G % k == 0 and G // k >= 2]
    for _ in range(40):
        k = rng.choice(ks) if (ks and rng.random() < 0.6) else 1
        m = G // k
        if k == 1:
            r = 1
        else:
            rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs:
                continue
            r = rng.choice(rs)
        order, mul, inv = lib.semidirect_group(m, k, r)
        return _Group(order, mul, inv)
    return None


def _unreached(adj, N, src, D):
    """Number of vertices at distance more than D from src."""
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
    return N - cnt


def _cost(grp, S, D):
    """Unreached pairs from a_identity and b_identity. Zero means diameter <= D."""
    G = grp.G
    cols = [grp.col(s) for s in S]
    icols = [grp.col(grp.inv(s)) for s in S]
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        adj[g] = [G + c[g] for c in cols]
    for x in range(G):
        adj[G + x] = [c[x] for c in icols]
    return _unreached(adj, N, 0, D) + _unreached(adj, N, G, D)


def _anneal(grp, d, D, rng, deadline):
    """Simulated annealing over connection sets S (|S| = d, 0 in S). Returns S or None."""
    G = grp.G
    if d - 1 > G - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cur = _cost(grp, S, D)
    T = 3.0
    while cur > 0:
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _cost(grp, T2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = T2, c2
        T = max(0.3, T * 0.998)
    return S if cur == 0 else None


def _edges(grp, S):
    G = grp.G
    E = []
    for s in S:
        c = grp.col(s)
        for g in range(G):
            E.append((g, G + c[g]))
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2 or d == 1:
        # K_{d,d} has diameter 2 (and is a single edge for d = 1).
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d}, which is the Haar graph with G = d.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_G = d
    moore = lib.moore_bound(d, D)
    hiG = moore // 2

    budget = 0.4
    while best_G < hiG:
        now = time.monotonic()
        rb = min(budget, deadline - now)
        if rb <= 0:
            break
        lo = best_G + 1
        G = rng.randint(lo, min(lo + 3, hiG))
        grp = _sample_group(G, rng)
        if grp is not None:
            S = _anneal(grp, d, D, rng, now + rb)
            if S is not None:
                n = 2 * G
                e = _edges(grp, S)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_e, best_G = n, e, G
                    budget = 0.4
                    continue
        budget = min(budget * 1.03, 6.0)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
