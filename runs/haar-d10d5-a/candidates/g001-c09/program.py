"""Haar-graph search for diameter 5 over metacyclic groups Z_m x|_r Z_k.

Idea (new in this version): vectorise the group multiplication as a numpy table,
then sweep group orders N upward from d. For each N, a few random non-abelian
metacyclic groups are tried with a simulated-annealing search over the connection
set S. The cost of S counts uncovered elements of (S^-1 S)^2 and (S S^-1)^2.
Cost 0 means diameter <= 5, and the group of the largest success is kept.
"""
import math
import random
import time

import numpy as np

import lib


def _meta_group(m, k, r):
    """Multiplication table M (N x N, int32) and inverse array of Z_m x|_r Z_k.

    Element (a, b) is coded as a*k + b, and (a,b)(c,d) = (a + r^b c, b + d).
    Requires r^k = 1 (mod m) and gcd(r, m) = 1.
    """
    N = m * k
    x = np.arange(N, dtype=np.int64)
    A, B = x // k, x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    first = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    second = (B[:, None] + B[None, :]) % k
    M = (first * k + second).astype(np.int32)
    nb = (-B) % k
    inv = ((-pw[nb] * A) % m) * k + nb  # inverse of (a,b) is (-r^{-b} a, -b)
    return N, M, inv.astype(np.int64)


def _candidates(N, rng):
    """Random non-abelian metacyclic groups of order N (plus cyclic for small N)."""
    out = set()
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.add((m, k, r))
    lst = sorted(out)
    rng.shuffle(lst)
    lst = lst[:3]
    if N <= 60:
        lst.append((N, 1, 1))  # cyclic fallback, only for small orders
    return lst


def _anneal(N, M, inv, d, rng, deadline):
    """Find a d-subset S of the group with zero cost, or return None at the deadline."""

    def cost(S):
        Si = inv[S]
        total = 0
        for P in (M[Si[:, None], S[None, :]].ravel(),
                  M[S[:, None], Si[None, :]].ravel()):
            W = np.unique(P)
            sq = M[W[:, None], W[None, :]].ravel()
            cov = np.zeros(N, dtype=bool)
            cov[sq] = True
            total += N - int(cov.sum())
        return total

    while time.monotonic() < deadline:
        S = np.array(rng.sample(range(N), d), dtype=np.int64)
        c = cost(S)
        L, T0 = 3000, 1.5
        for step in range(L):
            if c == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            T = T0 * (0.02 / T0) ** (step / L)
            i = rng.randrange(d)
            g = rng.randrange(N)
            if (S == g).any():
                continue
            old = S[i]
            S[i] = g
            c2 = cost(S)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                c = c2
            else:
                S[i] = old
        if c == 0:
            return S
    return None


def _haar_group_graph(N, M, S, d):
    """Bipartite graph: A-vertex g joined to B-vertex N + s*g for s in S."""
    us = np.tile(np.arange(N, dtype=np.int64), d)
    vs = N + np.concatenate([M[int(s)] for s in S]).astype(np.int64)
    return 2 * N, list(zip(us.tolist(), vs.tolist()))


def _cyclic_fallback(d, D, seed, deadline):
    """Parent-style cyclic Haar search, used for cases other than D = 5."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D != 5 or d < 3:
        return _cyclic_fallback(d, D, seed, deadline)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    best_half = d

    N = d
    while N <= 7000 and time.monotonic() < deadline - 0.2:
        found = None
        for (m, k, r) in _candidates(N, rng)[:3]:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            cap = max(0.3, min(3.0, remaining / 6.0))
            NN, M, inv = _meta_group(m, k, r)
            S = _anneal(NN, M, inv, d, rng, min(deadline, now + cap))
            if S is not None:
                found = (NN, M, S)
                break
        if found is not None:
            NN, M, S = found
            if NN > best_half:
                n, edges = _haar_group_graph(NN, M, S, d)
                if lib.is_valid(n, edges, d, D):
                    best, best_half = (n, edges), NN
        N += 1
    return best
