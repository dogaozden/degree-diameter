"""Haar-graph annealing over metacyclic groups of order just above 2000, for the d=10, D=5 target.

NEW IDEA.  A Haar graph on a group G with connection set S (|S| = d) has 2|G| vertices. It has diameter
at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. The search anneals S to drive the number of uncovered
group elements to zero. Groups are metacyclic Z_m x| Z_k of order N = m*k with N > 2000, so the graph
has more than 4000 vertices. Several such groups are cycled, each annealing run gets a time slice, and
the largest graph that passes lib.is_valid is kept.

The parent used random bipartite regular graphs and only a fixed Haar fallback. This program uses
exact coverage cost on non-abelian groups instead.

SAFETY.  Every returned graph passes lib.is_valid. A verified smaller Haar graph (order 3582) is the
fallback. Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)

# Verified smaller Haar graph on Z_199 x| Z_9 (order 3582); used only as a fallback.
FALLBACK_PARAMS = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def meta_table(m, k, lam):
    """Multiplication table of Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l).

    Returns (MT, inv) where MT[x, y] = x*y and inv[x] is the inverse of x (identity is element 0).
    """
    N = m * k
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        A = (a[lo:hi, None] + pw[j[lo:hi]][:, None] * a[None, :]) % m
        B = (j[lo:hi, None] + j[None, :]) % k
        MT[lo:hi] = A * k + B
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidate_groups(count=6, lo_order=2001, hi_order=2200):
    """Non-abelian metacyclic groups (m, k, lam) of order N in [lo_order, hi_order), smallest orders first."""
    out = []
    for N in range(lo_order, hi_order):
        for k in range(2, 41):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = None
            for c in range(2, m):
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1:
                    lam = c
                    break
            if lam is None:
                continue
            out.append((m, k, lam))
            if len(out) >= count:
                return out
    return out


def make_cost(MT, inv, N):
    """Cost = uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2. Zero iff diameter <= 5."""
    def cost(S):
        Si = inv[S]
        T = np.unique(MT[Si[:, None], S[None, :]])
        T2 = MT[T[:, None], T[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[T2] = True
        c1 = N - int(mark.sum())
        U = np.unique(MT[S[:, None], Si[None, :]])
        U2 = MT[U[:, None], U[None, :]].ravel()
        mark2 = np.zeros(N, dtype=bool)
        mark2[U2] = True
        return c1 + N - int(mark2.sum())
    return cost


def anneal(cost, N, d, rng, t_end, temp0=3.0, temp1=0.05):
    """Simulated annealing over d-element subsets of the group. Returns (best_cost, best_S)."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = cost(S)
    best = (cur, S.copy())
    if cur == 0:
        return best
    t_start = time.monotonic()
    span = max(1e-3, t_end - t_start)
    while True:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t_start) / span
        temp = temp0 * (temp1 / temp0) ** frac
        i = int(rng.integers(d))
        cand = None
        for _ in range(4):
            g = int(rng.integers(N))
            if g in S:
                continue
            S2 = S.copy()
            S2[i] = g
            c = cost(S2)
            if cand is None or c < cand[0]:
                cand = (c, S2)
        if cand is None:
            continue
        c, S2 = cand
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = S2, c
            if cur < best[0]:
                best = (cur, S.copy())
                if cur == 0:
                    break
    return best


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, edge (g, A) ~ (s*g, B) for s in S."""
    g = np.arange(N, dtype=np.int64)
    parts = [np.stack([g, N + MT[int(s)].astype(np.int64)], axis=1) for s in S]
    E = np.concatenate(parts)
    return 2 * N, [(int(a), int(b)) for a, b in E]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget

    best = None
    try:
        MT, _ = meta_table(*FALLBACK_PARAMS)
        n, edges = haar_edges(MT, FALLBACK_S, MT.shape[0])
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        best = None

    rng = np.random.default_rng(seed)
    groups = candidate_groups(count=6)
    tables = {}
    slice_len = 4.0
    idx = 0
    while groups and time.monotonic() + 1.0 < deadline:
        key = idx % len(groups)
        idx += 1
        try:
            if key not in tables:
                tables[key] = meta_table(*groups[key])
            MT, inv = tables[key]
            N = MT.shape[0]
            cost = make_cost(MT, inv, N)
            t_end = min(deadline, time.monotonic() + slice_len)
            c, S = anneal(cost, N, d, rng, t_end)
            if c == 0:
                n, edges = haar_edges(MT, S, N)
                if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
        except Exception:
            continue

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
