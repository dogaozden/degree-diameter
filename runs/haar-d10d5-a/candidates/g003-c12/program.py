"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

CONSTRUCTION.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G|
vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the cost of S is the number
of uncovered elements in those two sets, and the graph is valid exactly when the cost is 0.

SEARCH.  Non-abelian metacyclic groups Z_m x|_lam Z_k with order just above the record half-size (2001+) are
tried in round-robin.  Each gets a simulated-annealing run on S (one slot replaced per move, with restarts
when stale).  Once a cost-0 set is found, the Haar graph is verified with lib.is_valid.  Later searches
then only target larger group orders.

SAFETY.  A valid smaller Haar fallback (order 3582) is verified first.  Only graphs that pass lib.is_valid are
returned.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

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


def candidate_groups(lo, hi, cap):
    """Up to cap groups (N, m, k, lam) with N in [lo, hi), non-abelian (lam != 1), k >= 3, one per N."""
    out = []
    for N in range(lo, hi):
        found = None
        for k in range(3, N // 3 + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    found = (N, m, k, lam)
                    break
            if found is not None:
                break
        if found is not None:
            out.append(found)
            if len(out) >= cap:
                break
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
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    A = MT[Si[:, None], S[None, :]].ravel()
    W = MT[A[:, None], A[None, :]].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[W] = True
    c = N - int(np.count_nonzero(mark))
    B = MT[S[:, None], Si[None, :]].ravel()
    W2 = MT[B[:, None], B[None, :]].ravel()
    mark2 = np.zeros(N, dtype=bool)
    mark2[W2] = True
    return c + N - int(np.count_nonzero(mark2))


def anneal(MT, inv, N, d, end, rng):
    """Search for S with cost 0 before time `end`.  Returns S (int64 array) or None."""
    while time.monotonic() < end:
        S = rng.choice(np.arange(1, N), size=d, replace=False).astype(np.int64)
        cur = cost(MT, inv, S, N)
        best_c = cur
        T = 2.0
        stale = 0
        while cur > 0 and stale < 4000 and time.monotonic() < end:
            i = int(rng.integers(d))
            g = int(rng.integers(1, N))
            if g in S:
                continue
            S2 = S.copy()
            S2[i] = g
            c2 = cost(MT, inv, S2, N)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = S2, c2
            if cur < best_c:
                best_c = cur
                stale = 0
            else:
                stale += 1
            T = max(0.3, T * 0.999)
        if cur == 0:
            return S
    return None


# ----------------------------------------------------------------------------- small valid graphs

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


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

    best_half = best[0] // 2 if best is not None else 0

    cands = candidate_groups(2001, 2200, 8)
    cache = {}
    slice_len = 3.0
    try:
        while time.monotonic() < deadline - 0.5:
            pending = [c for c in cands if c[0] > best_half]
            if not pending:
                break
            for c in pending:
                if time.monotonic() >= deadline - 0.5:
                    break
                N, m, k, lam = c
                if c not in cache:
                    cache = {key: v for key, v in cache.items() if key[0] > best_half}
                    cache[c] = group_meta(m, k, lam)
                MT, inv = cache[c]
                end = min(deadline, time.monotonic() + slice_len)
                S = anneal(MT, inv, N, d, end, rng)
                if S is not None:
                    res = checked(MT, sorted(int(s) for s in S), d, D)
                    if res is not None:
                        best = res
                        best_half = N
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
