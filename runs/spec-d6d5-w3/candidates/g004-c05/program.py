"""Voltage-lift search over small bipartite base graphs, plus safe fallbacks.

Design:
- Fallbacks (always valid): K_{d,d}, PG(2,d-1) incidence, Araujo-Pardo-Lopez graph.
- Main search (D >= 4): take a small base graph of max degree d and diameter <= 3
  (PG(2,q) with q the largest prime power <= d-1, and the Araujo-Pardo-Lopez graph),
  then lift it over a random group G with one voltage per base edge. The lift
  keeps degree and bipartiteness. Diameter is checked by BFS from one fibre
  representative per base vertex, which is exact because the group acts regularly
  on each fibre. Voltages are annealed to minimise unreached pairs.
- Every returned graph is re-checked with lib.is_valid.

This version has not been benchmarked. The lift search is new, and its success
on the d=6, D=5 target is unverified.
"""
import math
import random
import time

import numpy as np

import lib


def _deadline_for(time_limit, start):
    return start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))


def _haar_fallback(d):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _prep_base(n, E, d):
    """Slot bookkeeping for a base graph: each base edge gets a slot index at each endpoint."""
    deg = [0] * n
    su = [0] * len(E)
    sv = [0] * len(E)
    for i, (u, v) in enumerate(E):
        su[i] = deg[u]
        deg[u] += 1
        sv[i] = deg[v]
        deg[v] += 1
    if max(deg, default=0) > d or not lib.is_bipartite(n, E):
        return None
    return (n, [(int(u), int(v)) for u, v in E], su, sv)


def _group_options(G):
    """All (m, k, r) with G = m*k giving a semidirect product Z_m x| Z_k."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            rs = [1 % m]
        elif m == 1:
            rs = [0]
        else:
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        for r in rs:
            opts.append((m, k, r))
    return opts


def _pick_group(G, rng):
    """Right-multiplication table PT[s, x] = x*s for a random group of order G."""
    opts = _group_options(G)
    if not opts:
        return None
    m, k, r = opts[rng.randrange(len(opts))]
    order, mul, _ = lib.semidirect_group(m, k, r)
    if order != G:
        return None
    return np.array([[mul(x, s) for x in range(G)] for s in range(G)], dtype=np.int64)


class _Lift:
    """Voltage lift of a base graph. Lifted vertex (u, x) has index u*G + x; index Nr is a dummy."""

    def __init__(self, base, G, PT, W):
        self.nb, self.E, self.su, self.sv = base
        self.G = G
        self.PT = PT
        self.W = W
        self.Nr = self.nb * G
        self.nbr = np.full((self.Nr + 1, W), self.Nr, dtype=np.int64)
        self.fib = np.arange(G, dtype=np.int64)
        self.volt = [0] * len(self.E)

    def set(self, e, s):
        u, v = self.E[e]
        A = u * self.G + self.fib
        B = v * self.G + self.PT[s]
        self.nbr[A, self.su[e]] = B
        self.nbr[B, self.sv[e]] = A
        self.volt[e] = s

    def cost(self, D):
        """Number of (base representative, vertex) pairs at distance > D."""
        S, Nr, G = self.nb, self.Nr, self.G
        reach = np.zeros((S, Nr + 1), dtype=bool)
        reach[np.arange(S), np.arange(S) * G] = True
        for _ in range(D):
            reach = reach | reach[:, self.nbr].any(axis=2)
        return S * Nr - int(reach[:, :Nr].sum())

    def edges(self):
        out = set()
        for a in range(self.Nr):
            for b in self.nbr[a]:
                b = int(b)
                if b < self.Nr and a < b:
                    out.add((a, b))
        return sorted(out)


def _search_lift(base, G, PT, d, D, rng, deadline):
    L = _Lift(base, G, PT, d)
    m = len(L.E)
    for e in range(m):
        L.set(e, rng.randrange(G))
    cost = L.cost(D)
    T = 3.0
    while cost > 0 and time.monotonic() < deadline:
        e = rng.randrange(m)
        old = L.volt[e]
        new = rng.randrange(G)
        if new == old:
            continue
        L.set(e, new)
        c2 = L.cost(D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            L.set(e, old)
        T = max(0.5, T * 0.9995)
    return L if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = _deadline_for(time_limit, start)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _haar_fallback(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and d >= 2:
        try:
            bases = []
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    prep = _prep_base(*lib.projective_plane_incidence(q), d)
                    if prep is not None:
                        bases.append(prep)
                    break
            ar = _araujo(d)
            if ar is not None:
                prep = _prep_base(ar[0], ar[1], d)
                if prep is not None:
                    bases.append(prep)

            while bases and time.monotonic() < deadline:
                base = bases[rng.randrange(len(bases))]
                nb = base[0]
                G_lo = max(2, best_n // nb + 1)
                G = G_lo + rng.choice([0, 0, 0, 1, 1, 2])
                PT = _pick_group(G, rng)
                if PT is None:
                    continue
                remain = deadline - time.monotonic()
                slice_t = min(remain, 10.0)
                if slice_t <= 0.5:
                    break
                L = _search_lift(base, G, PT, d, D, rng,
                                 time.monotonic() + slice_t)
                if L is not None:
                    consider(L.Nr, L.edges())
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _haar_fallback(d)
    return best
