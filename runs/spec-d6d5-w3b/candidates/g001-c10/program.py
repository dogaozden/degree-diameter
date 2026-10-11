"""Bold rewrite: Haar graphs over (semi)direct products, searched by annealing.

Replaces the earlier voltage-lift search with a different family. For a group G of
order n and a connection set S of size d containing the identity, the Haar graph
joins A_g to B_{g s} for every s in S. Left translation is transitive on each side,
so the diameter is the larger eccentricity of A_e and B_e. That makes each cost
evaluation two numpy BFS runs. Fallbacks (K_{d,d}, PG(2,q), Araujo-Pardo-Lopez) are
kept and checked with lib.is_valid, so every case still returns a valid graph.
Risk: the old multi-base lift search that produced the 624 on d6D5 is removed.
"""
import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _sample_group(G, rng):
    """Random group of order G: cyclic, or Z_m x| Z_k with r^k = 1 mod m (r = 1 gives a direct product)."""
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        return lib.cyclic_group(m)
    cands = [1]
    if m > 2:
        for r in rng.sample(range(2, m), min(m - 2, 80)):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(r)
    r = rng.choice(cands)
    try:
        return lib.semidirect_group(m, k, r)
    except ValueError:
        return None


class _Haar:
    """Haar graph of a group G: A_g ~ B_{g s} for s in S. Identity is 0 in every group used here."""

    def __init__(self, G, mul, inv, d, D):
        self.G, self.mul, self.inv, self.d, self.D = G, mul, inv, d, D
        self._R = {}

    def right(self, s):
        r = self._R.get(s)
        if r is None:
            mul, G = self.mul, self.G
            r = np.array([mul(x, s) for x in range(G)], dtype=np.int64)
            self._R[s] = r
        return r

    def cost(self, S):
        """Unreached (source, vertex) pairs from A_e and B_e within distance D. Zero iff valid."""
        G, D = self.G, self.D
        invS = [self.inv(s) for s in S]
        total = 0
        for src in (0, G):
            seen = np.zeros(2 * G, dtype=bool)
            seen[src] = True
            fr = np.array([src], dtype=np.int64)
            for _ in range(D):
                parts = []
                A = fr[fr < G]
                B = fr[fr >= G] - G
                if A.size:
                    for s in S:
                        parts.append(G + self.right(s)[A])
                if B.size:
                    for t in invS:
                        parts.append(self.right(t)[B])
                if not parts:
                    break
                cand = np.unique(np.concatenate(parts))
                cand = cand[~seen[cand]]
                if cand.size == 0:
                    break
                seen[cand] = True
                fr = cand
            total += 2 * G - int(seen.sum())
        return total

    def search(self, rng, deadline):
        """Hill-climb a connection set S (size d, containing 0) with zero cost, or return None."""
        G, d = self.G, self.d
        if G < d:
            return None
        S = [0] + rng.sample(range(1, G), d - 1)
        c = self.cost(S)
        while c > 0 and time.monotonic() < deadline:
            i = rng.randrange(1, d)
            x = rng.randrange(1, G)
            if x in S:
                continue
            T = S[:]
            T[i] = x
            ct = self.cost(T)
            if ct <= c or rng.random() < 0.02:
                S, c = T, ct
        return S if c == 0 else None


def _haar_phase(d, D, deadline, rng, start_n, consider, moore):
    """Increase the group order G from start_n/2 upward, searching a valid Haar graph at each G."""
    G = max(d, start_n // 2 + 1)
    while time.monotonic() < deadline and 2 * G <= moore:
        found = None
        slice_end = min(deadline, time.monotonic() + 1.5)
        for _ in range(4):
            if time.monotonic() >= slice_end:
                break
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul, inv = g
            H = _Haar(order, mul, inv, d, D)
            S = H.search(rng, slice_end)
            if S is not None:
                found = (H, S)
                break
        if found is not None:
            H, S = found
            n = 2 * H.G
            edges = [(x, H.G + H.mul(x, s)) for x in range(H.G) for s in S]
            consider(n, edges)
        G += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if d >= 2:
        _haar_phase(d, D, deadline, rng, best_n, consider, lib.moore_bound(d, D))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
