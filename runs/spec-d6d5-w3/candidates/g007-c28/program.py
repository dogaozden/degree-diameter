"""Bipartite (d, D)-graph construction with a Haar-graph-over-groups search.

Main family (new in this version): Haar graphs H(G, S) over a finite group G.
Vertices are A_g and B_h for g, h in G; A_g ~ B_h iff g^{-1} h is in S, with
|S| = d. Left multiplication by G is an automorphism that preserves both sides,
so the diameter check needs only two BFS runs (from A_e and from B_e). The group
is a cyclic group or a metacyclic semidirect product Z_m x| Z_k. Connection sets
are found by simulated annealing. Every candidate is checked with lib.is_valid
before it is accepted.

Baselines (complete bipartite K_{d,d}, projective-plane incidence, Araujo-Pardo-Lopez)
are kept as safe fallbacks. Nothing unverified is returned.
"""
import math
import random
import time

import lib


def _haar_search(G, mul, inv, d, D, rng, deadline, iters):
    """Anneal a d-subset S of group G so that H(G, S) has diameter <= D.

    Returns S on success, otherwise None.
    """
    N = 2 * G
    rp = {}
    inv_of = [inv(x) for x in range(G)]

    def R(x):
        r = rp.get(x)
        if r is None:
            r = [mul(g, x) for g in range(G)]
            rp[x] = r
        return r

    def cost(S):
        Rs = [R(s) for s in S]
        Ris = [R(inv_of[s]) for s in S]
        adj = [None] * N
        for g in range(G):
            adj[g] = [G + r[g] for r in Rs]
        for h in range(G):
            adj[G + h] = [r[h] for r in Ris]
        total = 0
        for src in (0, G):
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
            total += N - cnt
        return total

    S = rng.sample(range(G), d)
    c = cost(S)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = cost(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.05, T * 0.998)
    return S if c == 0 else None


def _groups(G, rng, cap=3):
    """Cyclic group of order G plus a few semidirect products Z_m x| Z_k with m*k = G."""
    out = [lib.cyclic_group(G)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append(lib.semidirect_group(m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _haar_edges(G, mul, S):
    """Edge list of H(G, S) with A_g = g and B_h = G + h."""
    edges = []
    for s in S:
        for g in range(G):
            edges.append((g, G + mul(g, s)))
    return 2 * G, edges


def _best_pg(d):
    """Projective-plane incidence graph of PG(2, q) for the largest prime power q <= d-1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # Algebraic baselines (diameter 3, valid for all D >= 3).
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    q_ar = d - 2
    if q_ar >= 3 and lib.is_prime_power(q_ar):
        try:
            ar = lib.araujo_lopez_graph(q_ar)
            consider(ar[0], ar[1])
        except Exception:
            pass

    # Main search: Haar graphs over cyclic and metacyclic groups.
    moore = lib.moore_bound(d, D)
    top = moore // 2  # |G| <= moore/2 because n = 2|G|
    while time.monotonic() < deadline:
        base_lo = best_n // 2 + 1
        if base_lo > top:
            break
        if D >= 5 and rng.random() < 0.5:
            lo = max(base_lo, int(top * 0.42))
        else:
            lo = base_lo
        hi = min(top, lo + 40)
        if lo > hi:
            lo = base_lo
            hi = min(top, lo + 40)
        if d > lo:
            # Need |G| >= d to choose d distinct elements.
            lo = d
            hi = max(hi, lo)
        G = rng.randint(lo, hi)

        for order, mul, inv in _groups(G, rng):
            if time.monotonic() >= deadline:
                break
            slice_end = min(deadline, time.monotonic() + 5.0)
            S = _haar_search(order, mul, inv, d, D, rng, slice_end, 1500)
            if S is not None:
                n, e = _haar_edges(order, mul, S)
                consider(n, e)
                break

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
