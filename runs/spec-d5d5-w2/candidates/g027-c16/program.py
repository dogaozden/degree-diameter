import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 4000     # annealing steps per (group, base size) attempt
DUP_PENALTY = 50        # cost added per repeated (i, j, voltage) dart
_RT_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4 (projective plane, quadrangle).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Base graph: k A-vertices and k B-vertices, d layers. Each layer is a perfect
# matching P[L] from A-base to B-base, with a voltage S[L, i] per dart.
# Lifted vertices: A_(i,g) and B_(j,x), with A_(i,g) ~ B_(P[L,i], g * S[L,i]).
# Left multiplication is an automorphism, so one representative per base
# vertex suffices for the diameter check.
#
# The cost is the number of unreached (representative, vertex) pairs within
# distance D, plus a penalty for repeated darts (which would give multi-edges).
# Each cost evaluation is numpy BFS over the full lift.
# ----------------------------------------------------------------------------

def _groups(G):
    """Semidirect parameters (m, k, r) with m * k = G and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    """Cached (order, RT, RTinv): RT[s, g] = g*s and RTinv[s, x] = x*s^-1, as numpy arrays."""
    key = (m, k, r)
    hit = _RT_CACHE.get(key)
    if hit is not None:
        return hit
    G, mul, inv = lib.semidirect_group(m, k, r)
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        RT[s] = [mul(g, s) for g in range(G)]
    invs = np.array([inv(s) for s in range(G)], dtype=np.int64)
    RTinv = RT[invs]
    val = (G, RT, RTinv)
    if len(_RT_CACHE) > 24:
        _RT_CACHE.clear()
    _RT_CACHE[key] = val
    return val


def _adjacency(k, G, RT, RTinv, P, S):
    """Neighbour array of shape (2kG, d): column L is the layer-L neighbour of each vertex."""
    d = P.shape[0]
    N = 2 * k * G
    adj = np.empty((N, d), dtype=np.int64)
    for L in range(d):
        for i in range(k):
            j = int(P[L, i])
            s = int(S[L, i])
            adj[i * G:(i + 1) * G, L] = (k + j) * G + RT[s]
            adj[(k + j) * G:(k + j + 1) * G, L] = i * G + RTinv[s]
    return adj


def _score(k, G, D, RT, RTinv, P, S):
    """Zero iff the lift is simple and has diameter <= D (cost counts unreached pairs)."""
    d = P.shape[0]
    seen = set()
    dup = 0
    for L in range(d):
        for i in range(k):
            t = (i, int(P[L, i]), int(S[L, i]))
            if t in seen:
                dup += 1
            else:
                seen.add(t)
    adj = _adjacency(k, G, RT, RTinv, P, S)
    N = adj.shape[0]
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        reached = np.zeros(N, dtype=bool)
        reached[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            mask = np.zeros(N, dtype=bool)
            mask[adj[frontier].ravel()] = True
            mask &= ~reached
            if not mask.any():
                break
            reached |= mask
            frontier = np.flatnonzero(mask)
        total += N - int(np.count_nonzero(reached))
    return total + DUP_PENALTY * dup


def _anneal(d, D, k, G, RT, RTinv, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer matchings; returns (P, S) with cost 0 or None."""
    P = np.zeros((d, k), dtype=np.int64)
    S = np.zeros((d, k), dtype=np.int64)
    for L in range(d):
        P[L] = rng.sample(range(k), k)
        S[L] = [rng.randrange(G) for _ in range(k)]
    cost = _score(k, G, D, RT, RTinv, P, S)
    T0, T1 = 3.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))
        L = rng.randrange(d)
        if rng.random() < 0.6:
            i = rng.randrange(k)
            old = int(S[L, i])
            new = rng.randrange(G)
            if new == old:
                continue
            S[L, i] = new
            c2 = _score(k, G, D, RT, RTinv, P, S)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / temp):
                cost = c2
            else:
                S[L, i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L, a], P[L, b] = P[L, b], P[L, a]
            c2 = _score(k, G, D, RT, RTinv, P, S)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / temp):
                cost = c2
            else:
                P[L, a], P[L, b] = P[L, b], P[L, a]
    if cost == 0:
        return P, S
    return None


def _edges(k, G, RT, P, S):
    """Edge list of the lift; A-vertices are 0..kG-1, B-vertices follow."""
    d = P.shape[0]
    E = set()
    for L in range(d):
        for i in range(k):
            j = int(P[L, i])
            s = int(S[L, i])
            for g in range(G):
                E.add((i * G + g, (k + j) * G + int(RT[s, g])))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= moore or d < 2:
        return best

    # Main search: multi-base annealed lifts over semidirect products,
    # climbing the target order after each success.
    try:
        while time.monotonic() < deadline and best[0] < moore:
            ks = [k for k in (2, 3, 4) if 2 * k * (best[0] // (2 * k) + 1) <= moore]
            if not ks:
                break
            k = rng.choice(ks)
            lo = best[0] // (2 * k) + 1
            G = lo + rng.randrange(3)
            if 2 * k * G > moore:
                G = lo
            m, k2, r = rng.choice(_groups(G))
            Gord, RT, RTinv = _group_tables(m, k2, r)
            res = _anneal(d, D, k, Gord, RT, RTinv, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                P, S = res
                n, E = _edges(k, Gord, RT, P, S)
                consider(n, E)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
