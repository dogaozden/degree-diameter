import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline candidates (small, deterministic, always validated).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over finite groups.
#
# Group G acts on both sides by right multiplication. Vertices A_g = g and
# B_h = G + h, and A_g ~ B_{g*s} for each s in a connection set S with |S| = d.
# This is d-regular and bipartite. Left multiplication is an automorphism,
# so the eccentricities of A_e and B_e determine the diameter exactly.
# The search is over the connection set S of a (possibly non-abelian) group.
# ----------------------------------------------------------------------------

class _Group:
    """Finite group of order G (elements 0..G-1, identity 0), with cached right-multiplication maps."""

    def __init__(self, order, mul, inv):
        self.G = order
        self._mul = mul
        self._inv = inv
        self._right = {}
        self._rinv = {}

    def right(self, s):
        """Permutation g -> g*s."""
        p = self._right.get(s)
        if p is None:
            mul = self._mul
            p = [mul(g, s) for g in range(self.G)]
            self._right[s] = p
        return p

    def right_inv(self, s):
        """Permutation h -> h*s^{-1}; the A-neighbours of B_h are A_{h*s^{-1}}."""
        p = self._rinv.get(s)
        if p is None:
            mul = self._mul
            si = self._inv(s)
            p = [mul(h, si) for h in range(self.G)]
            self._rinv[s] = p
        return p


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G (k2 = 1 gives the cyclic group)."""
    k_opts = [k for k in range(1, G) if G % k == 0 and G // k >= 3]
    if not k_opts:
        return None
    k2 = rng.choice(k_opts)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(2, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    order, mul, inv = lib.semidirect_group(m, k2, r)
    return _Group(order, mul, inv)


def _uncovered(G, Pl, Il, D):
    """Number of (source, vertex) pairs at distance > D, for sources A_e and B_e."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for p in Pl:
                        v = G + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for p in Il:
                        v = p[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _search(d, D, grp, rng, deadline):
    """Anneal a connection set S of size d in the group so the bi-Cayley graph has diameter <= D."""
    G = grp.G
    if G < d + 1:
        return None
    S = rng.sample(range(G), d)

    def cost(T):
        return _uncovered(G, [grp.right(s) for s in T],
                          [grp.right_inv(s) for s in T], D)

    c = cost(S)
    T = 3.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = cost(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.998)
    return S if c == 0 else None


def _lift_edges(grp, S):
    """Edges of the bi-Cayley graph for connection set S."""
    G = grp.G
    E = []
    for s in S:
        p = grp.right(s)
        for g in range(G):
            E.append((g, G + p[g]))
    return 2 * G, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)

    try:
        if D >= 3:
            for make in (_pg_candidate, _araujo_candidate):
                cand = make(d)
                if cand is not None:
                    consider(cand[0], cand[1])

        # Main search: bi-Cayley graphs over (non-abelian) groups near the target order.
        while time.monotonic() < deadline and best_n < moore:
            frac = rng.uniform(0.3, 0.45)
            lo = max(best_n // 2 + 1, int(frac * moore / 2), d + 1)
            G = rng.randint(lo, lo + 25)
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            local_deadline = min(deadline, time.monotonic() + 3.0)
            S = _search(d, D, grp, rng, local_deadline)
            if S is not None:
                n, e = _lift_edges(grp, S)
                consider(n, e)
    except Exception:
        pass  # keep whatever valid graph we already have

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
