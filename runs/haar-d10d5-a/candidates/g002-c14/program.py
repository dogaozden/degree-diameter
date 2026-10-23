"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over non-abelian groups.

CONSTRUCTION.  Haar graph of a group G with connection set S (|S| = d): vertices A_g and B_g for g in G,
with edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, has 2|G| vertices, and for diameter <= 5
it suffices that (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost counts uncovered group elements.

SEARCH.  Groups are metacyclic Z_m x| Z_k of order just above 2000 (the record is 4000 = 2 * 2000).  For each
group, simulated annealing replaces one element of S at a time, minimizing the cost.  Random restarts cover
stalls.  Any cost-0 candidate is verified exactly with lib.is_valid before it is returned.

SAFETY.  The parent's valid Haar graph (order 3582) is verified first and kept as the fallback.  Other (d, D)
cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a multiplication table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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


def candidate_groups(rng, max_count=40):
    """Metacyclic groups Z_m x| Z_k with order 2001..2040 and a nontrivial action, in shuffled order."""
    out = []
    for N in range(2001, 2041):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
                    break
            if len(out) >= max_count:
                break
        if len(out) >= max_count:
            break
    rng.shuffle(out)
    return out


# ----------------------------------------------------------------------------- Haar graphs

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


def cost(MT, inv, S, N):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2."""
    iS = inv[S]
    P1 = np.unique(MT[iS[:, None], S[None, :]])
    P2 = np.unique(MT[S[:, None], iS[None, :]])
    c = 0
    for P in (P1, P2):
        prod = MT[P[:, None], P[None, :]].ravel()
        c += N - int(np.count_nonzero(np.bincount(prod, minlength=N)))
    return c


def anneal(MT, inv, N, d, rng, t_end):
    """Anneal a connection set S of size d in the group. Returns S with cost 0, or None at t_end."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    c = cost(MT, inv, S, N)
    run_best = c
    stall = 0
    T = 0.5
    while True:
        if c == 0:
            return S
        if time.monotonic() > t_end:
            return None
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if x in S:
            continue
        old = int(S[i])
        S[i] = x
        c2 = cost(MT, inv, S, N)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
            if c < run_best:
                run_best = c
                stall = 0
            else:
                stall += 1
        else:
            S[i] = old
            stall += 1
        if stall > 3000:
            # Restart from a fresh random set to escape the basin.
            S = rng.choice(N, size=d, replace=False).astype(np.int64)
            c = cost(MT, inv, S, N)
            run_best = c
            stall = 0


# ----------------------------------------------------------------------------- small valid graphs

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
TARGET = (10, 5)


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------- entry point

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

    try:
        groups = candidate_groups(rng)
        gi = 0
        while groups and time.monotonic() + 1.0 < deadline:
            m, k, lam = groups[gi % len(groups)]
            gi += 1
            N = m * k
            MT, inv = group_meta(m, k, lam)
            t_end = min(deadline - 1.0, time.monotonic() + 6.0)
            S = anneal(MT, inv, N, d, rng, t_end)
            if S is not None:
                n, edges = haar_edges(MT, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    return n, edges
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
