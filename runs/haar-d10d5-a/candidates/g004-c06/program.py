"""Bipartite degree-diameter search for the d=10, D=5 target using Haar graphs over non-abelian groups.

CONSTRUCTION.  For a finite group G and a connection set S of size d, the Haar graph has vertices
(g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular
on 2|G| vertices.  Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  The cost of S is the number of group elements missing from those two squared sets.  The graph
is valid exactly when the cost is 0.  Groups are metacyclic Z_m x| Z_k with k >= 2 and a non-trivial
action.  Their orders run from just above the known Haar record (|G| = 1791) up to 2060, which beats
the target record 4000 at |G| > 2000.  For each candidate group, a local search over S (single-slot
swaps with Metropolis acceptance and random restarts) runs for a short slice.  The largest order found
wins.

SAFETY.  A valid Haar fallback (order 3582) is verified first.  Every result is checked with lib.is_valid
before being returned.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


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
    return _finish(MT)


def candidate_groups(N):
    """All (m, k, lam) with m*k = N, k >= 2, m >= 2, lam a non-trivial unit with lam^k = 1 mod m."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ cost and local search

def cost(MT, inv, S):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2."""
    N = MT.shape[0]
    Sinv = inv[S]
    E1 = np.unique(MT[Sinv[:, None], S[None, :]].ravel())
    c1 = N - np.unique(MT[E1[:, None], E1[None, :]].ravel()).size
    E2 = np.unique(MT[S[:, None], Sinv[None, :]].ravel())
    c2 = N - np.unique(MT[E2[:, None], E2[None, :]].ravel()).size
    return int(c1 + c2)


def local_search(MT, inv, d, rng, deadline, patience=4000, T=0.6):
    """Search S of size d with cost 0 by single-slot swaps and random restarts.  Returns S or None."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        c = cost(MT, inv, S)
        stale = 0
        while c > 0 and stale < patience and time.monotonic() < deadline:
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if x in S:
                stale += 1
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = cost(MT, inv, S2)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, c = S2, c2
            stale = 0 if c2 < c + delta or delta < 0 else stale + 1
        if c == 0:
            return S
    return None


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    # Candidate group orders N (graph order 2N), ascending, starting just below the current best.
    # A graph of order 2N beats the target record 4000 once N > 2000.
    start_N = (best[0] // 2 + 1) if best is not None else 1792
    cands = []
    for N in range(max(start_N, 1792), 2061):
        groups = candidate_groups(N)
        rng.shuffle(groups)
        cands.extend((N, g) for g in groups[:12])

    best_N = best[0] // 2 if best is not None else 0
    for N, (m, k, lam) in cands:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        if N <= best_N:
            continue
        try:
            MT, inv = group_meta(m, k, lam)
            S = local_search(MT, inv, d, rng, time.monotonic() + min(2.0, remaining))
            if S is not None:
                res = checked(MT, S, d, D)
                if res is not None:
                    best = res
                    best_N = N
        except Exception:
            continue

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
