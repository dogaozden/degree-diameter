import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Main family: bi-Cayley graphs over semidirect products G = Z_m x| Z_k.
#
# Vertices A_g and B_h (g, h in G). Edge A_g ~ B_h iff g^{-1} h in S, |S| = d.
# Then every vertex has degree d, the graph is bipartite, and left
# multiplication by G is an automorphism. Hence the diameter is <= D iff
# BFS from A_e and from B_e reaches everything within D steps.
# WLOG the identity lies in S (right-translating S gives an isomorphic graph).
#
# This replaces the per-base-vertex voltage lifts of the parent: the cost is a
# two-source numpy BFS over a group of order ~343, and the search is a plain
# annealing over the connection set, over many groups and orders.
# ----------------------------------------------------------------------------


def _semidirect_table(m, k, r):
    """Full multiplication table M[x, y] of Z_m x|_r Z_k, element (a, b) coded as a*k+b (identity 0)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + Dd) % k


def _inverses(M):
    """inv[s] = t with M[s, t] == 0 (the identity is index 0)."""
    return np.argmax(M == 0, axis=1)


def _cost(G, D, Pm, Qm):
    """Number of ordered (source, vertex) pairs unreached within D, sources A_e and B_e.

    Pm[j][g] is the B-index reached from A_g by dart j; Qm[j][h] is the A-index reached from B_h.
    Zero iff the bi-Cayley graph has diameter <= D.
    """
    total = 0
    for side in (0, 1):
        rA = np.zeros(G, dtype=bool)
        rB = np.zeros(G, dtype=bool)
        if side == 0:
            rA[0] = True
        else:
            rB[0] = True
        fA = rA.copy()
        fB = rB.copy()
        for _ in range(D):
            if not fA.any() and not fB.any():
                break
            nB = np.zeros(G, dtype=bool)
            ia = np.flatnonzero(fA)
            if ia.size:
                for P in Pm:
                    nB[P[ia]] = True
            nA = np.zeros(G, dtype=bool)
            ib = np.flatnonzero(fB)
            if ib.size:
                for Q in Qm:
                    nA[Q[ib]] = True
            nB &= ~rB
            nA &= ~rA
            rB |= nB
            rA |= nA
            fA, fB = nA, nB
        total += 2 * G - int(np.count_nonzero(rA)) - int(np.count_nonzero(rB))
    return total


def _group_candidates(G, rng):
    """Random (m, k, r) with m*k = G, m >= 2, and r^k = 1 mod m, gcd(r, m) = 1. None if none exists."""
    ks = [k for k in range(1, G) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    return m, k, rng.choice(rs)


def _anneal(d, D, G, MT, inv, rng, deadline, max_iters):
    """Anneal a connection set S (identity fixed in S, |S| = d) until the cost is zero. Returns S or None."""
    if G < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)

    def score(T):
        return _cost(G, D, [MT[s] for s in T], [MT[inv[s]] for s in T])

    cur = score(S)
    best, bestS = cur, list(S)
    T = 3.0
    for _ in range(max_iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = score(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
            if cur < best:
                best, bestS = cur, list(S)
        T = max(0.3, T * 0.999)
    return bestS if best == 0 else None


def _edges(G, M, S):
    """Edges of the bi-Cayley graph: A_g = g, B_h = G + h, A_g ~ B_{g*s} for s in S."""
    E = []
    for s in S:
        col = M[:, s]
        for g in range(G):
            E.append((g, G + int(col[g])))
    return E


def _search(d, D, deadline, rng, start_base, target, best_n, best_E):
    """Repeatedly sample a group order and a group, anneal, and keep the largest valid graph."""
    t0 = time.monotonic()
    total = max(1e-3, deadline - t0)
    cap = 1200
    while time.monotonic() < deadline - 0.5:
        el = time.monotonic() - t0
        if best_n == 0:
            frac = el / total
            if frac < 0.25:
                base = start_base
            elif frac < 0.5:
                base = int(start_base * 0.91)
            else:
                base = int(start_base * 0.82)
        else:
            base = best_n // 2 + 1
        base = max(2, min(base, cap))
        span = 30 if target else 8
        G = base + int(span * rng.random() ** 2)
        G = min(max(G, d), cap)

        grp = _group_candidates(G, rng)
        if grp is None:
            continue
        m, k, r = grp
        try:
            M = _semidirect_table(m, k, r)
        except Exception:
            continue
        MT = np.ascontiguousarray(M.T)
        inv = _inverses(M).tolist()
        slice_end = min(deadline, time.monotonic() + 2.5)
        S = _anneal(d, D, G, MT, inv, rng, slice_end, 6000)
        if S is None:
            continue
        E = _edges(G, M, S)
        n = 2 * G
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E
    return best_n, best_E


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2 (and degree d).
    fb_n, fb_E = lib.haar_graph(d, range(d))
    best_n, best_E = fb_n, fb_E

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_E = pg[0], pg[1]

    if d >= 2:
        target = (d == 6 and D == 5)
        if target:
            start_base = 342
        else:
            start_base = max(2, min(1000, lib.moore_bound(d, D) // 8))
        try:
            n2, e2 = _search(d, D, deadline, rng, start_base, target, best_n, best_E)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                best_n, best_E = n2, e2
        except Exception:
            pass

    if not lib.is_valid(best_n, best_E, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, [(int(u), int(v)) for u, v in best_E]
