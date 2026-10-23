"""Bipartite degree-diameter search for the d=10, D=5 target, using annealed Haar graphs.

CONSTRUCTION.  Haar graph of a group G and a connection set S (|S| = d): vertices (g, A) and (g, B),
edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost of S is the number of group elements missed by those
two sets.  The graph is valid exactly when the cost is 0.

NEW HELPERS.
  * cover_cost: the uncovered count for both squared sets, computed with fancy indexing on the
    multiplication table.
  * pick_group: samples metacyclic groups Z_m x|_lam Z_k of order 2000..2160 with lam != 1, so the
    group is non-abelian.  Non-abelian groups waste fewer words.
  * anneal: Metropolis search on S.  Each move either replaces one element with a random group element
    or with a product of two current elements.  The search restarts when it stalls.

SAFETY.  A valid smaller Haar graph (order 3582) is checked first and kept as the baseline.  A new graph
replaces it only if it has more vertices and passes lib.is_valid.  Other (d, D) cases return a small
always-valid graph.
"""
import math
import time

import numpy as np

import lib

TEMP = 0.6
TARGET = (10, 5)


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


def pick_group(rng):
    """Random metacyclic group (m, k, lam) with order in [2000, 2160] and lam a nontrivial unit of order dividing k."""
    for _ in range(20000):
        k = int(rng.integers(2, 80))
        lo = max(3, 2000 // k)
        hi = 2160 // k + 1
        if hi <= lo:
            continue
        m = int(rng.integers(lo, hi))
        N = m * k
        if N < 2000 or N > 2160:
            continue
        lam = int(rng.integers(2, m))
        if lam == 1 or math.gcd(lam, m) != 1:
            continue
        if pow(lam, k, m) != 1 % m:
            continue
        return m, k, lam
    return None


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


def cover_cost(MT, inv, S):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2.  Zero iff diameter <= 5."""
    N = MT.shape[0]
    A = np.unique(MT[inv[S][:, None], S[None, :]])   # S^-1 S
    B = np.unique(MT[S[:, None], inv[S][None, :]])   # S S^-1
    cost = 0
    for T in (A, B):
        P = MT[T[:, None], T[None, :]].ravel()
        covered = np.zeros(N, dtype=bool)
        covered[P] = True
        cost += N - int(covered.sum())
    return cost


# ----------------------------------------------------------------------------- annealing

def anneal(MT, inv, d, deadline, rng, stall_limit=3000):
    """Metropolis search over d-subsets S with a product-neighbour move.  Returns (best_cost, best_S)."""
    N = MT.shape[0]
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = cover_cost(MT, inv, S)
    best_cost, best_S = cur, S.copy()
    stall = 0
    while best_cost > 0 and time.monotonic() < deadline:
        i = int(rng.integers(d))
        if rng.random() < 0.5:
            cand = int(rng.integers(N))
        else:
            j, l = rng.integers(d, size=2)
            cand = int(MT[S[j], S[l]])
        if np.any(S == cand):
            continue
        old = S[i]
        S[i] = cand
        c = cover_cost(MT, inv, S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            if c < best_cost:
                best_cost, best_S = c, S.copy()
                stall = 0
                continue
        else:
            S[i] = old
        stall += 1
        if stall > stall_limit:
            S = rng.choice(N, size=d, replace=False).astype(np.int64)
            cur = cover_cost(MT, inv, S)
            stall = 0
    return best_cost, best_S


# ----------------------------------------------------------------------------- small fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# ------------------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None
    best_n = best[0] if best is not None else 0

    while time.monotonic() + 2.0 < deadline:
        grp = pick_group(rng)
        if grp is None:
            break
        try:
            MT, inv = group_meta(*grp)
        except Exception:
            continue
        slice_end = min(deadline - 1.0, time.monotonic() + 15.0)
        try:
            cost, S = anneal(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if cost == 0:
            try:
                n, edges = haar_edges(MT, S)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_n = n
            except Exception:
                pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
