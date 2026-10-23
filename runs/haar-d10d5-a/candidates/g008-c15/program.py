"""Bipartite degree-diameter search for the d=10, D=5 target, using annealed Haar graphs over non-abelian groups.

CONSTRUCTION.  For a finite group G (here Z_m x|_lam Z_k) and a connection set S of d distinct elements,
the Haar graph has vertices (g, A) and (g, B) for g in G, with (g, A) ~ (s*g, B) for s in S.  It is
bipartite and d-regular on 2|G| vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  For each group order N = |G| just above the current best (starting from the valid fallback),
try a few non-abelian groups of order N.  For each one, simulated annealing moves one element of S at a
time and minimises cost(S) = uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.
Cost 0 means the graph has diameter at most 5.  Each cost evaluation uses boolean masks, not sorting.

SAFETY.  The fallback (order 3582) is verified first.  Any candidate must pass lib.is_valid before it is
returned.  Other (d, D) cases return a small always-valid graph.
"""
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidate_groups(N, pyrng, limit):
    """Non-abelian semidirect products Z_m x|_lam Z_k of order N (lam != 1), shuffled, at most `limit`."""
    out = []
    for m in range(2, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) != 1:
                continue
            if pow(lam, k, m) != 1 % m:
                continue
            out.append((m, k, lam))
    pyrng.shuffle(out)
    return out[:limit]


# ----------------------------------------------------------------------------- Haar graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    if len({int(s) for s in S}) != d:
        return None
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- annealing

def cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2.  Zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    m1 = np.zeros(N, dtype=bool)
    m1[MT[Si[:, None], S[None, :]].ravel()] = True
    P1 = np.flatnonzero(m1)
    c1 = np.zeros(N, dtype=bool)
    c1[MT[np.ix_(P1, P1)].ravel()] = True

    m2 = np.zeros(N, dtype=bool)
    m2[MT[S[:, None], Si[None, :]].ravel()] = True
    P2 = np.flatnonzero(m2)
    c2 = np.zeros(N, dtype=bool)
    c2[MT[np.ix_(P2, P2)].ravel()] = True
    return (N - int(c1.sum())) + (N - int(c2.sum()))


def anneal(MT, inv, d, N, rng, t_end, T=0.8):
    """Anneal a connection set of d distinct elements until cost 0 or t_end.  Returns S or None."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    c = cost(MT, inv, S, N)
    it = 0
    while c > 0:
        it += 1
        if it % 256 == 0 and time.monotonic() >= t_end:
            return None
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if x in S:
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = cost(MT, inv, S2, N)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
    return S


def search(d, D, deadline, rng, pyrng, best):
    """Try group orders N = lo+1, lo+2, ... with a few groups each; keep the largest valid Haar graph found."""
    SLICE = 3.0
    lo = best[0] // 2 if best is not None else 0
    N = lo + 1
    while time.monotonic() + 1.0 < deadline and N <= lo + 400:
        found = None
        for (m, k, lam) in candidate_groups(N, pyrng, 2):
            if time.monotonic() + 1.0 >= deadline:
                break
            MT, inv = group_meta(m, k, lam)
            t_end = min(deadline, time.monotonic() + SLICE)
            S = anneal(MT, inv, d, N, rng, t_end)
            if S is not None:
                res = checked(MT, S, d, D)
                if res is not None:
                    found = res
                    break
        if found is not None:
            best = found
        N += 1
    return best


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    pyrng = random.Random(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        found = search(d, D, deadline, rng, pyrng, best)
        if found is not None:
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
