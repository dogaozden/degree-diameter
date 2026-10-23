"""Haar-graph tabu search over metacyclic groups for the bipartite degree-diameter problem (d=10, D=5).

NEW IDEA (not in the parent).  The parent anneals voltage lifts over several orbits.  This program instead
searches single-orbit Haar graphs with a TABU search over the connection set S, with two new ingredients:

  * Left-normalisation: replacing S by gS gives an isomorphic Haar graph, so the identity is fixed in S.
  * Word-product moves: a candidate replacement is a product of two elements of S union S^-1, not a uniform
    random element.  This targets the uncovered elements of (S^-1 S)^2 and (S S^-1)^2 much faster.
  * Tabu with aspiration: recently removed elements are tabu for a short tenure unless they reach a new best.

Graph: vertices A_g = g and B_g = N + g, with A_g ~ B_{s*g} for s in S.  By the criterion
(S^-1 S)^2 = G and (S S^-1)^2 = G, the diameter is at most 5 exactly when the cost is 0.  Every zero-cost
set is checked with lib.is_valid before it is accepted.

RATCHET.  The group order N is chosen just above best_n // 2, so each success raises the bar.  The
validated fallback (order 1791, 3582 vertices) is always kept, so the output is never worse than the parent.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

CANDIDATES_PER_STEP = 16
PATIENCE = 2500


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def metacyclic_params(N):
    """All non-abelian (m, k, r) with m*k = N, r^k = 1 mod m, gcd(r, m) = 1, r >= 2."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv) with MT[x, y] = x*y and inv[x] = x^-1.
    """
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 256
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


# ------------------------------------------------------------------------------ cost

def covered_cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  Zero iff diameter <= 5."""
    iS = inv[S]
    Q = np.unique(MT[iS[:, None], S[None, :]])   # s_i^-1 s_j
    P = np.unique(MT[S[:, None], iS[None, :]])   # s_i s_j^-1
    c = 0
    for X in (Q, P):
        sq = MT[X[:, None], X[None, :]].ravel()
        cov = np.zeros(N, dtype=bool)
        cov[sq] = True
        c += N - int(np.count_nonzero(cov))
    return c


# ------------------------------------------------------------------------------ search

def tabu_search(MT, inv, N, d, rng, deadline, patience):
    """Tabu search on S (identity fixed in slot 0).  Returns a zero-cost S as an array, or None."""
    S = np.empty(d, dtype=np.int64)
    S[0] = 0
    S[1:] = rng.choice(np.arange(1, N), d - 1, replace=False)
    cur = covered_cost(MT, inv, S, N)
    best = cur
    last_imp = 0
    tabu = np.zeros(N, dtype=np.int64)
    it = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return S.copy()
        it += 1
        if it - last_imp > patience:
            return None
        W = np.concatenate([S, inv[S]])
        in_S = set(S.tolist())
        t = 1 + int(rng.integers(d - 1))
        bc, bv = -1, None
        for _ in range(CANDIDATES_PER_STEP):
            c = int(MT[W[int(rng.integers(2 * d))], W[int(rng.integers(2 * d))]])
            if c == 0 or c in in_S:
                continue
            old = int(S[t])
            S[t] = c
            v = covered_cost(MT, inv, S, N)
            S[t] = old
            if tabu[c] > it and v >= best:
                continue
            if bv is None or v < bv or (v == bv and rng.random() < 0.5):
                bv, bc = v, c
        if bc < 0:
            continue
        old = int(S[t])
        S[t] = bc
        tabu[old] = it + 8 + int(rng.integers(8))
        cur = bv
        if cur < best:
            best = cur
            last_imp = it
    return None


def haar_from(MT, S, N):
    """Haar graph of the table group: A-vertex g is g, B-vertex g is N + g, with A_g ~ B_{s*g}."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    while time.monotonic() < deadline:
        N = best_n // 2 + 1 + int(rng.integers(0, 12))
        params = metacyclic_params(N)
        if not params:
            continue
        m, k, r = params[int(rng.integers(len(params)))]
        MT, inv = group_table(m, k, r)
        S = tabu_search(MT, inv, N, d, rng, deadline, PATIENCE)
        if S is None:
            continue
        if 2 * N <= best_n:
            continue
        try:
            n2, e = haar_from(MT, S, N)
            if lib.is_valid(n2, e, d, D):
                best_n, best_edges = n2, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
