import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1: projective plane incidence graph PG(2, d-1), degree d, diameter 3.
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """PG(2, q) incidence graph with q = d - 1 when q is a prime power (degree d, diameter 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 2 (bold change): Haar graphs H(G, S) over finite groups G of order
# near the record. Vertices a_g = g and b_x = G + x; a_g ~ b_{g s} for s in S,
# |S| = d. Left multiplication is an automorphism that is transitive on each
# side, so diameter <= D reduces to checking two BFS balls, from a_e and b_e.
# S can be taken to contain the identity (right translation is an isomorphism).
# Groups are semidirect products Z_m x| Z_k from lib.semidirect_group.
# ----------------------------------------------------------------------------

def _group_options(G):
    """All (m, k, r) with m * k = G giving Z_m x| Z_k (m >= 2)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


class _Group:
    """A group of order G with cached right-multiplication permutations."""

    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def pair(self, s):
        """(P, Q): P[g] = g*s on A-side indices, Q[x] = x*s^{-1} for B-side indices."""
        p = self.cache.get(s)
        if p is None:
            G, mul = self.G, self.mul
            si = self.inv(s)
            P = [mul(g, s) for g in range(G)]
            Q = [mul(x, si) for x in range(G)]
            p = (P, Q)
            self.cache[s] = p
        return p


def _unreached(G, Ps, Qs, src, D):
    """Number of vertices of the Haar graph not within distance D of src."""
    N = 2 * G
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                for P in Ps:
                    v = G + P[u]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                x = u - G
                for Q in Qs:
                    v = Q[x]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return N - count


def _cost(G, Ps, Qs, D):
    """Zero iff H(G, S) has diameter <= D (checked from a_e and b_e only)."""
    return _unreached(G, Ps, Qs, 0, D) + _unreached(G, Ps, Qs, G, D)


def _anneal(G, grp, d, D, rng, deadline, iters):
    """Search S (identity included, |S| = d) with H(G, S) of diameter <= D. Returns S or None."""
    S = [0] + rng.sample(range(1, G), d - 1)
    pairs = [grp.pair(s) for s in S]
    cur = _cost(G, [p[0] for p in pairs], [p[1] for p in pairs], D)
    T = 1.5
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        s_new = rng.randrange(1, G)
        if s_new in S:
            continue
        pairs2 = pairs[:]
        pairs2[i] = grp.pair(s_new)
        c2 = _cost(G, [p[0] for p in pairs2], [p[1] for p in pairs2], D)
        T = max(0.02, T * 0.995)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S[i] = s_new
            pairs = pairs2
            cur = c2
    return S if cur == 0 else None


def _haar_edges(G, S, grp):
    """Edge list of H(G, S): a_g ~ b_{g s} for s in S."""
    edges = []
    for s in S:
        P, _ = grp.pair(s)
        for g in range(G):
            edges.append((g, G + P[g]))
    return edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (Haar graph of Z_d with all shifts), diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _pg_incidence(d)
        if pg is not None:
            consider(pg[0], pg[1])
            return best_n, best_e

    # Main search: Haar graphs over non-cyclic groups of order just above the current best half.
    rng = random.Random(seed * 1000003 + d * 101 + D)
    while time.monotonic() < deadline:
        target = best_n // 2
        G = max(d + 1, target + 1 + rng.randrange(0, 4))
        opts = _group_options(G)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        order, mul, inv = lib.semidirect_group(m, k, r)
        grp = _Group(order, mul, inv)
        S = _anneal(order, grp, d, D, rng, deadline, 600)
        if S is not None:
            consider(2 * order, _haar_edges(order, S, grp))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
