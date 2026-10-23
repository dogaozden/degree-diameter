"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over non-abelian groups.

NEW CONSTRUCTION (not in the parent).  For a finite group G and a connection set S of d elements, the Haar
graph has vertices (g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite,
d-regular, has 2|G| vertices, and its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  So the
search minimises cost(S) = uncovered(S^-1 S, squared) + uncovered(S S^-1, squared) by simulated annealing
over S, with best-of-K replacement moves.  Groups are semidirect products Z_m x|_lam Z_k with orders just
above 2000, so the resulting graphs can beat the record of 4000.

ROUTINE DETAILS.
  - Each move replaces one element of S with one of K random group elements, keeping the best candidate.
  - The cost is evaluated with bincount over the d^2 and d^4 word products, using the group multiplication
    table.
  - Groups are tried in turn, each for a fixed time slice, so no single group absorbs the whole budget.

SAFETY.  A valid Haar fallback (order 3582) is verified first.  Every candidate is checked with lib.is_valid
before it replaces the best graph.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
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


def _group_candidates(rng, orders):
    """Non-abelian semidirect candidates (m, k, lam) with m*k in orders, small k, lam != 1."""
    out = []
    for N in orders:
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
            if not lams:
                continue
            picks = rng.permutation(len(lams))[:2]
            for p in picks:
                out.append((m, k, lams[int(p)]))
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


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- annealing over S

def _cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  Zero means diameter <= 5."""
    Si = inv[S]
    P = MT[Si[:, None], S[None, :]].ravel().astype(np.int64)
    P2 = MT[P[:, None], P[None, :]].ravel()
    Q = MT[S[:, None], Si[None, :]].ravel().astype(np.int64)
    Q2 = MT[Q[:, None], Q[None, :]].ravel()
    c1 = N - np.count_nonzero(np.bincount(P2, minlength=N))
    c2 = N - np.count_nonzero(np.bincount(Q2, minlength=N))
    return int(c1 + c2)


def anneal(MT, inv, N, d, rng, end, K=6):
    """Best-of-K annealing over connection sets S of size d until cost 0 or time `end`."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = _cost(MT, inv, S, N)
    best_S, best_c = S.copy(), cur
    T = 1.0
    while cur > 0 and time.monotonic() < end:
        i = int(rng.integers(d))
        cand_S, cand_c = None, None
        for _ in range(K):
            g = int(rng.integers(N))
            if np.any(S == g):
                continue
            T2 = S.copy()
            T2[i] = g
            c = _cost(MT, inv, T2, N)
            if cand_c is None or c < cand_c:
                cand_S, cand_c = T2, c
        if cand_c is None:
            continue
        if cand_c <= cur or rng.random() < math.exp(-(cand_c - cur) / T):
            S, cur = cand_S, cand_c
            if cur < best_c:
                best_S, best_c = S.copy(), cur
        T = max(0.3, T * 0.999)
    return best_S, best_c


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

    try:
        cands = _group_candidates(rng, range(2001, 2041))
        cands.sort(key=lambda c: c[0] * c[1])
        if cands:
            slice_len = max(4.0, budget / 8.0)
            idx = 0
            while time.monotonic() + 2.0 < deadline:
                m, k, lam = cands[idx % len(cands)]
                idx += 1
                N = m * k
                if best is not None and 2 * N <= best[0]:
                    continue
                MT, inv = group_meta(m, k, lam)
                end = min(deadline, time.monotonic() + slice_len)
                S, c = anneal(MT, inv, N, d, rng, end)
                if c == 0:
                    got = checked(MT, S, d, D)
                    if got is not None and (best is None or got[0] > best[0]):
                        best = got
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
