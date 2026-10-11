import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Haar graphs of finite groups (bold change: group-theoretic Haar search).
#
# H(G, S): left vertices a_x, right vertices b_y, edge a_x -- b_{x*s} for s in S.
# Left translations x -> g*x are automorphisms and act transitively on each side,
# so the diameter is at most D iff a_0 and b_0 both reach every vertex within D.
# Each group of order G gives a graph on 2G vertices, degree |S| = d.
# We search groups of order just above the current best, which ratchets upward.
# ----------------------------------------------------------------------------


def _missing(adj, src, D):
    """Number of vertices not within distance D of src."""
    N = len(adj)
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
    return N - count


class _Haar:
    """Haar graph of a finite group given by (order, mul, inv)."""

    def __init__(self, order, mul, inv):
        self.G = order
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def _cols(self, s):
        c = self.cache.get(s)
        if c is None:
            G, mul = self.G, self.mul
            si = self.inv(s)
            c = ([mul(x, s) for x in range(G)], [mul(y, si) for y in range(G)])
            self.cache[s] = c
        return c

    def adjacency(self, S):
        G = self.G
        Rs = [self._cols(s)[0] for s in S]
        Ls = [self._cols(s)[1] for s in S]
        adjA = [[G + R[x] for R in Rs] for x in range(G)]
        adjB = [[L[y] for L in Ls] for y in range(G)]
        return adjA + adjB

    def cost(self, S, D):
        adj = self.adjacency(S)
        return _missing(adj, 0, D) + _missing(adj, self.G, D)

    def search(self, d, D, rng, deadline):
        """Anneal a d-element set S until the Haar graph has diameter <= D. Returns S or None."""
        G = self.G
        if G < d:
            return None
        S = rng.sample(range(G), d)
        c = self.cost(S, D)
        t0 = time.monotonic()
        span = max(1e-3, deadline - t0)
        while c > 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = 0.2 + 1.3 * (1.0 - (now - t0) / span)
            i = rng.randrange(d)
            t = rng.randrange(G)
            if t in S:
                continue
            S2 = S[:]
            S2[i] = t
            c2 = self.cost(S2, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
        return S if c == 0 else None

    def edges(self, S):
        G = self.G
        E = []
        for s in S:
            R = self._cols(s)[0]
            for x in range(G):
                E.append((x, G + R[x]))
        return 2 * G, E


def _group_options(G, rng, max_r=6):
    """(m, k, r) triples for semidirect products Z_m x| Z_k of order G (k = 1 gives cyclic)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > max_r:
            rs = rng.sample(rs, max_r)
        opts.extend((m, k, r) for r in rs)
    return opts


def _make_group(m, k, r):
    if k == 1:
        return lib.cyclic_group(m)
    return lib.semidirect_group(m, k, r)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            return True
        return False

    if d == 2 and D >= 2:
        consider(*lib.haar_graph(D, [0, 1]))  # cycle C_{2D}

    if D >= 3 and d >= 3:
        # Projective plane incidence with the largest prime power q <= d - 1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        # Araujo-Pardo-Lopez graph for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if best_n >= moore:
        return best

    if D >= 3 and d >= 3:
        half_moore = moore // 2
        budget_each = max(1.5, 0.06 * time_limit)
        while time.monotonic() < deadline and best_n < moore:
            lo = best_n // 2 + 1
            if lo > half_moore:
                break
            hi = min(half_moore, lo + max(2, lo // 10))
            G = rng.randint(lo, hi)
            opts = _group_options(G, rng)
            if not opts:
                continue
            m, k, r = rng.choice(opts)
            try:
                order, mul, inv = _make_group(m, k, r)
            except ValueError:
                continue
            now = time.monotonic()
            budget = min(budget_each, deadline - now)
            if budget <= 0:
                break
            hs = _Haar(order, mul, inv)
            S = hs.search(d, D, rng, now + budget)
            if S is not None:
                consider(*hs.edges(S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
