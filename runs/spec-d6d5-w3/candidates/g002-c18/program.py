import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite Cayley (bi-Cayley with one connection set) search.
#
# Group G of order n0 acts on two sides: side 0 vertex g is joined to side 1
# vertex g*s for every s in a connection set S with |S| = d. Left multiplication
# is an automorphism, so every same-side pair reduces to a distance from the
# identity on side 0 or side 1. Two BFS runs (from e_0 and e_1) therefore decide
# validity. The search anneals S over the group, minimizing unreached pairs.
# Groups are semidirect products Z_m x| Z_k (k = 1 gives cyclic groups).
# ----------------------------------------------------------------------------

class _Group:
    """Finite group on 0..order-1 with identity 0, given by mul and inv."""

    def __init__(self, order, mul, inv):
        self.order = order
        self._mul = mul
        self._inv = inv
        self._perms = {}

    def inv(self, x):
        return self._inv(x)

    def perm(self, x):
        """Right multiplication g -> g*x as a list (cached)."""
        p = self._perms.get(x)
        if p is None:
            mul = self._mul
            p = [mul(g, x) for g in range(self.order)]
            self._perms[x] = p
        return p


def _random_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, or None if sampling fails."""
    divs = [k for k in range(1, G) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(20):
        k = rng.choice(divs)
        m = G // k
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return _Group(order, mul, inv)
    return None


def _unreached(G, S, grp, D):
    """Number of ordered (root, vertex) pairs not within distance D, roots e_0 and e_1.

    Vertex ids: side 0 is g in 0..G-1, side 1 is G + h.
    Side-0 g adjacent to side-1 G + g*s. Side-1 h adjacent to side-0 h*s^-1.
    """
    perms = [grp.perm(s) for s in S]
    iperms = [grp.perm(grp.inv(s)) for s in S]
    N = 2 * G
    total = 0
    for root in (0, G):
        seen = bytearray(N)
        seen[root] = 1
        frontier = [root]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for p in perms:
                        v = G + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for p in iperms:
                        v = p[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
            if count == N:
                break
        total += N - count
    return total


def _search(G, d, D, grp, rng, deadline, iters):
    """Anneal a connection set S of d distinct elements; return S with zero cost, else None."""
    S = rng.sample(range(G), d)
    c = _unreached(G, S, grp, D)
    T = 1.5
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _unreached(G, S2, grp, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.998)
    return S if c == 0 else None


def _graph(G, S, grp):
    """Edge list of the bi-Cayley graph (n, edges)."""
    E = []
    for s in S:
        p = grp.perm(s)
        E.extend((g, G + p[g]) for g in range(G))
    return 2 * G, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        # K_{d,d} has diameter 2 and order 2d, matching the Moore bound.
        return lib.haar_graph(d, range(d))
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    target = lib._moore_bound(d, D)

    # Cheap algebraic constructions (diameter 3, valid for D >= 3).
    if lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
    if best_n >= target:
        return best_n, best_e
    if d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass
    if best_n >= target:
        return best_n, best_e

    # Main search: bi-Cayley graphs over random semidirect products, with the
    # group order kept just above the best order found so far.
    while time.monotonic() < deadline:
        lo = max(d + 1, best_n // 2 + 1)
        G = rng.randint(lo, lo + 10)
        grp = _random_group(G, rng)
        if grp is None:
            continue
        S = _search(G, d, D, grp, rng, deadline, 1500)
        if S is not None:
            n, e = _graph(G, S, grp)
            consider(n, e)
            if best_n >= target:
                break

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
