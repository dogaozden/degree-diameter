import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline constructions (valid fallbacks and the D = 3 record).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family for D >= 5: bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices A_g = g and B_h = G + h for g, h in the group H (|H| = G).
# A_g is adjacent to B_{g*s} for each s in S, where |S| = d and S is a set of
# distinct group elements. Left multiplication is an automorphism, so the
# graph is bipartite, d-regular and simple, and its diameter is at most D iff
# BFS from A_e and from B_e reaches everything within D steps. Every
# evaluation is therefore two numpy BFS runs on 2G vertices.
#
# The search climbs the order G one step at a time. For each G it samples a
# random group and runs simulated annealing over the connection set S. Every
# success is validated with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _tables(m, k, r):
    """Multiplication and inverse tables for Z_m x| Z_k, element (a, b) coded as a*k + b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return mul, inv


def _sample_group(G, rng):
    """Random group of order G: a semidirect product Z_m x| Z_k, or cyclic if none is found."""
    k = rng.choice(_divisors(G))
    m = G // k
    if k >= 2 and m >= 2:
        for _ in range(60):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return _tables(m, k, r)
    return _tables(G, 1, 1)


def _cost(G, mul, inv, S, D):
    """Number of (source, vertex) pairs at distance > D, from A_e and from B_e. Zero means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    A2B = mul[:, Sa]        # A_g -> B_{g s}
    B2A = mul[:, inv[Sa]]   # B_h -> A_{h s^-1}
    total = 0
    for side in (0, 1):
        seenA = np.zeros(G, dtype=bool)
        seenB = np.zeros(G, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = seenA.copy()
            fB = np.zeros(G, dtype=bool)
        else:
            seenB[0] = True
            fB = seenB.copy()
            fA = np.zeros(G, dtype=bool)
        for _ in range(D):
            nB = np.zeros(G, dtype=bool)
            ia = np.flatnonzero(fA)
            if ia.size:
                nB[A2B[ia].ravel()] = True
            nB &= ~seenB
            nA = np.zeros(G, dtype=bool)
            ib = np.flatnonzero(fB)
            if ib.size:
                nA[B2A[ib].ravel()] = True
            nA &= ~seenA
            seenA |= nA
            seenB |= nB
            fA, fB = nA, nB
            if not (fA.any() or fB.any()):
                break
        total += 2 * G - int(seenA.sum()) - int(seenB.sum())
    return total


def _search(d, D, G, mul, inv, rng, deadline, evals):
    """Anneal a d-element connection set S in the group so the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    cur = _cost(G, mul, inv, S, D)
    T = 2.0
    for _ in range(evals):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        c_new = rng.randrange(G)
        if c_new in S:
            continue
        T2 = S[:]
        T2[i] = c_new
        c2 = _cost(G, mul, inv, T2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = T2, c2
        T = max(0.2, T * 0.998)
    return S if cur == 0 else None


def _edges(G, mul, S):
    """Edge list of the bi-Cayley graph with connection set S over the given multiplication table."""
    Sa = np.asarray(S, dtype=np.int64)
    B = mul[:, Sa]
    E = []
    for g in range(G):
        for j in range(len(S)):
            E.append((g, G + int(B[g, j])))
    return 2 * G, E


def _bicayley_ladder(d, D, seed, deadline, consider):
    """Raise the order G one step at a time, searching random groups for each G."""
    rng = random.Random(seed)
    G = max(d, 2)
    while time.monotonic() < deadline:
        mul, inv = _sample_group(G, rng)
        S = _search(d, D, G, mul, inv, rng, deadline, 1200)
        if S is not None:
            n, e = _edges(G, mul, S)
            consider(n, e)
            G += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except Exception:
            pass

    if D >= 5 and d >= 2:
        _bicayley_ladder(d, D, seed, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
