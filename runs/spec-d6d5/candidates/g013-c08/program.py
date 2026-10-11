import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: K_{d,d} and the projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: k = 1 bi-Cayley graphs over small non-abelian groups.
#
# Groups: Z_m x| Z_k (semidirect, element (a, b) coded as a*k + b), or cyclic.
# Graph:  A_g ~ B_{g*s} for s in S, |S| = d, S a set of distinct group elements.
# Left multiplication by h is an automorphism fixing both sides setwise and
# acting transitively on each side, so diameter <= D reduces to two BFS runs
# from A_identity and B_identity. Cost = number of vertices left unreached.
# Search: simulated annealing over S, for group orders G = n/2 increasing.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Random group of order G as (mul, inv) with identity element 0."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    for _ in range(60):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            _, mul, inv = lib.cyclic_group(m)
            return mul, inv
        units = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not units:
            continue
        r = rng.choice(units)
        _, mul, inv = lib.semidirect_group(m, k, r)
        return mul, inv
    return None


class _BiCayley:
    def __init__(self, G, mul, inv, D):
        self.G = G
        self.mul = mul
        self.inv = inv
        self.D = D
        self.cache = {}

    def rperm(self, s):
        """Permutation g -> g * s, cached."""
        p = self.cache.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self.cache[s] = p
        return p

    def _adj(self, S):
        G = self.G
        perms = [self.rperm(s) for s in S]
        invperms = [self.rperm(self.inv(s)) for s in S]
        adj = [[G + p[g] for p in perms] for g in range(G)]
        adj += [[q[h] for q in invperms] for h in range(G)]
        return adj

    def _reach(self, adj, src, N):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(self.D):
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
        return count

    def cost(self, S):
        N = 2 * self.G
        adj = self._adj(S)
        return (N - self._reach(adj, 0, N)) + (N - self._reach(adj, self.G, N))

    def edges(self, S):
        G = self.G
        E = []
        for s in S:
            p = self.rperm(s)
            for g in range(G):
                E.append((g, G + p[g]))
        return E

    def anneal(self, d, rng, deadline):
        """Annealing over connection sets S of size d. Returns S with cost 0, or None."""
        G = self.G
        S = rng.sample(range(G), d)
        c = self.cost(S)
        T = 1.0
        while c > 0 and time.monotonic() < deadline:
            T = max(0.05, T * 0.998)
            i = rng.randrange(d)
            s_new = rng.randrange(G)
            if s_new in S:
                continue
            T2 = S[:]
            T2[i] = s_new
            c2 = self.cost(T2)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = T2, c2
        return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts over random small groups, growing the order.
    if d >= 2:
        slice_len = max(1.0, min(4.0, 0.1 * time_limit))
        G = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline:
            g = _random_group(G, rng)
            if g is None:
                G += 1
                continue
            mul, inv = g
            if G < d:
                G += 1
                continue
            lift = _BiCayley(G, mul, inv, D)
            slice_end = min(deadline, time.monotonic() + slice_len)
            S = lift.anneal(d, rng, slice_end)
            if S is not None:
                consider(2 * G, lift.edges(S))
                G += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
