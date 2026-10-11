import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallbacks: K_{d,d}, projective-plane incidence graphs and the
# Araujo-Pardo-Lopez graph for D = 3.
# ----------------------------------------------------------------------------

def _km_edges(d):
    """K_{d,d} with parts 0..d-1 and d..2d-1: diameter 2, valid for D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: Haar graphs over groups G (order m), a_g ~ b_{g s} for s in S,
# |S| = d. Such a graph has 2m vertices and is automatically bipartite and
# d-regular with no duplicate edges (the s are distinct).
#
# Left multiplication by h maps a_g -> a_{hg}, b_y -> b_{hy}, an automorphism.
# So A and B are each vertex-transitive, and the diameter is <= D iff a_0 and
# b_0 reach every vertex within D steps. Cost = unreached count from the two
# sources, so one evaluation is just two BFS passes.
#
# Search: simulated annealing over the d-subset S, for many groups of order
# just above the current best/2. Groups are Z_m x|_r Z_k (lib.semidirect_group).
# ----------------------------------------------------------------------------

def _reach(adj, N, src, D):
    """Number of vertices within distance D of src."""
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
    return cnt


def _sample_group(G, rng):
    """Random semidirect product Z_m x|_r Z_k of order G with k <= 12, or None."""
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    return order, mul, inv


class _Haar:
    """Haar graph over a group: cost evaluation with cached right-multiplication tables."""

    def __init__(self, G, mul, inv, D):
        self.G = G
        self.mul = mul
        self.inv_f = inv
        self.D = D
        self.cache = {}

    def right(self, s):
        """Table g -> g * s."""
        t = self.cache.get(s)
        if t is None:
            mul = self.mul
            t = [mul(g, s) for g in range(self.G)]
            self.cache[s] = t
        return t

    def adj(self, S):
        G = self.G
        adj = [[] for _ in range(2 * G)]
        for s in S:
            Rs = self.right(s)
            Ris = self.right(self.inv_f(s))  # b_y ~ a_{y s^{-1}}
            for g in range(G):
                adj[g].append(G + Rs[g])
                adj[G + g].append(Ris[g])
        return adj

    def cost(self, S):
        N = 2 * self.G
        adj = self.adj(S)
        ca = _reach(adj, N, 0, self.D)
        cb = _reach(adj, N, self.G, self.D)
        return (N - ca) + (N - cb)

    def edges(self, S):
        G = self.G
        out = []
        for s in S:
            Rs = self.right(s)
            for g in range(G):
                out.append((g, G + Rs[g]))
        return out


def _anneal(H, d, rng, deadline, iters):
    """Anneal a d-subset S of the group; returns (S, cost)."""
    G = H.G
    S = rng.sample(range(G), d)
    c = H.cost(S)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = H.cost(S2)
        T = max(0.05, T * 0.998)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
    return S, c


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = _km_edges(d)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # D = 2 and D = 3: the constructions above are the answer (no search).
    if D < 4:
        return best_n, best_e

    # Haar-over-group annealing for D >= 4.
    lo = best_n // 2 + 1
    while time.monotonic() < deadline:
        G = rng.randint(lo, lo + 6)
        if G < d:
            continue
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul, inv = g
        H = _Haar(order, mul, inv, D)
        S, c = _anneal(H, d, rng, deadline, 3000)
        if c == 0:
            if consider(2 * order, H.edges(S)):
                lo = best_n // 2 + 1

    if not lib.is_valid(best_n, best_e, d, D):
        return _km_edges(d)
    return best_n, best_e
