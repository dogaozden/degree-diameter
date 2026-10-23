import math
import random
import time
from math import gcd

import numpy as np
import lib


def _group_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (element (a, b) coded as a*k + b), plus inverses."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    A, B = idx // k, idx % k
    a = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    b = (B[:, None] + B[None, :]) % k
    T = (a * k + b).astype(np.int32)
    inv = (T == 0).argmax(axis=1).astype(np.int64)
    return T, inv


def _candidates(N, rng):
    """Candidate groups of order N: non-abelian metacyclic ones first (shuffled), cyclic last."""
    out = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        out += [(m, k, r) for r in rs[:2]]
    rng.shuffle(out)
    out.append((N, 1, 1))  # cyclic group
    return out


def _anneal(T, inv, N, d, rng, until):
    """Find a d-subset S of G with cost 0, where cost counts elements missed by (S^-1 S)^2 and (S S^-1)^2."""

    def cost(S):
        iS = inv[S]
        P = T[iS[:, None], S[None, :]].ravel()
        Q = T[P[:, None], P[None, :]].ravel()
        L = np.count_nonzero(np.bincount(Q, minlength=N))
        P2 = T[S[:, None], iS[None, :]].ravel()
        Q2 = T[P2[:, None], P2[None, :]].ravel()
        R = np.count_nonzero(np.bincount(Q2, minlength=N))
        return 2 * N - L - R

    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    c = cost(S)
    best, stall, temp = c, 0, 1.0
    while c > 0:
        if time.monotonic() >= until:
            return None
        if stall > 3000:  # stuck: random restart
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            c = cost(S)
            best, stall, temp = c, 0, 1.0
            continue
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = S.copy()
        S2[i] = g
        c2 = cost(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
        if c < best:
            best, stall = c, 0
        else:
            stall += 1
        temp = max(0.3, temp * 0.9995)
    return S


def _try_group(m, k, r, d, D, rng, until):
    """Anneal a connection set in the group and return a verified Haar graph, or None."""
    N = m * k
    T, inv = _group_table(m, k, r)
    S = _anneal(T, inv, N, d, rng, until)
    if S is None:
        return None
    # A-vertex g is g, B-vertex h is N + h; A-vertex g ~ B-vertex s*g for s in S.
    edges = []
    for s in S:
        row = T[int(s)].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    if lib.is_valid(2 * N, edges, d, D):
        return (2 * N, edges)
    return None


def _search_d5(d, D, seed, deadline):
    """Climb through group orders N, annealing a connection set at each; return the largest valid graph found."""
    rng = random.Random(seed)
    best = None
    N = 2 * d * d
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        ok = None
        for (m, k, r) in _candidates(N, rng)[:2]:
            now = time.monotonic()
            if now >= deadline:
                break
            until = min(deadline, now + 3.0)
            ok = _try_group(m, k, r, d, D, rng, until)
            if ok is not None:
                break
        if ok is not None:
            best = ok
            fails = 0
            N = int(N * 1.05) + 1
        else:
            fails += 1
            N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 5 and d >= 3:
        res = _search_d5(d, D, seed, deadline)
        if res is not None:
            return res
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
