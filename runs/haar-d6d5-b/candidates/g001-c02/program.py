import math
import random
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Haar graphs over finite groups, with an annealing search on the connection set.
#
# Vertices (g, A) and (g, B) for g in G; edges (g, A) ~ (s*g, B) for s in S.
# This is bipartite, d-regular, and has 2|G| vertices. Its diameter is at most 5
# iff (S^-1 S)^2 = G and (S S^-1)^2 = G. The cost counts uncovered elements of
# these two squared sets, so cost 0 means a valid graph. Groups are the
# non-abelian semidirect products Z_m x| Z_k, built with vectorised tables.
# ----------------------------------------------------------------------------


def _table(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    Bv = (b[:, None] + b[None, :]) % k
    M = A * k + Bv
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _cost(M, inv, N, S):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2."""
    S = np.asarray(S, dtype=np.int64)
    I = inv[S]
    P = np.unique(M[I[:, None], S[None, :]])
    W = M[P[:, None], P[None, :]].ravel()
    c1 = N - int(np.count_nonzero(np.bincount(W, minlength=N)))
    Q = np.unique(M[S[:, None], I[None, :]])
    W2 = M[Q[:, None], Q[None, :]].ravel()
    c2 = N - int(np.count_nonzero(np.bincount(W2, minlength=N)))
    return c1 + c2


def _anneal(M, inv, N, d, deadline, rng):
    """Anneal a size-d connection set containing the identity. Return a cost-0 set, or None at the deadline."""
    iters = 0
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(M, inv, N, S)
        best_seen = cur
        stall = 0
        while stall < 3000:
            if cur == 0:
                return S
            iters += 1
            if (iters & 127) == 0 and time.monotonic() >= deadline:
                return None
            j = rng.randrange(1, d)
            g = rng.randrange(1, N)
            if g in S:
                stall += 1
                continue
            S2 = S[:]
            S2[j] = g
            c = _cost(M, inv, N, S2)
            if c <= cur or rng.random() < math.exp(-(c - cur) / 0.5):
                S, cur = S2, c
            if cur < best_seen:
                best_seen = cur
                stall = 0
            else:
                stall += 1
    return None


def _groups(N, rng):
    """Candidate groups of order N: a few non-abelian Z_m x| Z_k, then the cyclic group."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
        if rs:
            out.append((m, k, rng.choice(rs)))
    rng.shuffle(out)
    out = out[:3]
    out.append((N, 1, 1))
    return out


def _pipeline(d, D, end, rng, best):
    """Search Haar graphs over growing group orders; return the largest valid graph found."""
    hi = min(1 + d * (d - 1) + d * (d - 1) ** 3, 1500)
    state = {"N": d, "best": best}

    def attempt(N, slice_s):
        for m, k, r in _groups(N, rng):
            now = time.monotonic()
            if now >= end:
                return False
            M, inv = _table(m, k, r)
            S = _anneal(M, inv, N, d, min(end, now + slice_s), rng)
            if S is None:
                continue
            edges = [(g, N + int(M[s, g])) for s in S for g in range(N)]
            if lib.is_valid(2 * N, edges, d, D):
                state["N"] = N
                state["best"] = (2 * N, edges)
                return True
        return False

    # Phase A: ascend through group orders, stopping after a run of failures.
    N, fails = d + 1, 0
    while N <= hi and time.monotonic() < end and fails < 6:
        fails = 0 if attempt(N, 0.8) else fails + 1
        N += 1

    # Phase B: spend the rest of the budget on longer attempts just above the best order.
    slice_s = 3.0
    while time.monotonic() < end and state["N"] < hi:
        for N in range(state["N"] + 1, min(hi, state["N"] + 6) + 1):
            if time.monotonic() >= end:
                break
            if N <= state["N"]:
                continue
            attempt(N, slice_s)
        slice_s = min(slice_s * 1.2, 12.0)
    return state["best"]


def _generic(d, D, end, rng, best):
    """Fallback for other diameters: random cyclic Haar graphs checked with within_diameter."""
    m, misses = d + 1, 0
    while time.monotonic() < end and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= end:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2
    try:
        if D == 5:
            best = _pipeline(d, D, end, rng, best)
        else:
            best = _generic(d, D, end, rng, best)
    except Exception:
        pass

    n, edges = best
    if not lib.is_valid(n, edges, d, D):
        return lib.haar_graph(d, range(d))
    return n, edges
