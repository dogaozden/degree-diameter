"""Haar graphs over matrix and metacyclic groups of order 1792..2400 for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a group G of order N and a connection set S of 10 distinct elements, the Haar graph has
vertices A_g, B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite, 10-regular, and has 2N vertices.
It has diameter <= 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.  The search uses non-abelian groups:
PGL(2,13) and SL(2,13) (both of order 2184, giving 4368 vertices) and random metacyclic groups Z_m x| Z_k.

SEARCH.  Simulated annealing over S with a full recomputation of the cost (uncovered group elements in the two
product sets) at each step, plus restarts when stalled.  Groups are visited round-robin in time slices.  Any
zero-cost S is checked with lib.is_valid before it is accepted.  The parent's valid Haar graph
(3582 vertices) is the starting fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
SLICE = 6.0
TEMP = 0.8
STALL_LIMIT = 15000


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (N, MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return N, MT, inv


def normalize(E, p):
    """Scale each column of a 4 x K matrix array so its first nonzero entry is 1 (projective normalization)."""
    lead = np.ones(E.shape[1], dtype=np.int64)
    for k in (3, 2, 1, 0):
        lead = np.where(E[k] != 0, E[k], lead)
    invtab = np.array([0] + [pow(x, p - 2, p) for x in range(1, p)], dtype=np.int64)
    return (E * invtab[lead][None, :]) % p


def matrix_group(p, kind):
    """PGL(2,p) ('pgl') or SL(2,p) ('sl') as a multiplication table.  Returns (N, MT, inv)."""
    r = np.arange(p, dtype=np.int64)
    A, B, C, Dd = [x.ravel() for x in np.meshgrid(r, r, r, r, indexing='ij')]
    det = (A * Dd - B * C) % p
    keep = (det == 1) if kind == 'sl' else (det != 0)
    E = np.stack([A[keep], B[keep], C[keep], Dd[keep]]).astype(np.int64)
    if kind == 'pgl':
        E = normalize(E, p)
    code = np.unique(((E[0] * p + E[1]) * p + E[2]) * p + E[3])
    N = len(code)
    idx = np.full(p ** 4, -1, dtype=np.int64)
    idx[code] = np.arange(N)
    els = np.stack([code // p ** 3, (code // p ** 2) % p, (code // p) % p, code % p])
    a, b, c, dd = els[0], els[1], els[2], els[3]
    MT = np.empty((N, N), dtype=np.int32)
    for g in range(N):
        a0, b0, c0, d0 = (int(x) for x in els[:, g])
        e = np.stack([(a0 * a + b0 * c) % p,
                      (a0 * b + b0 * dd) % p,
                      (c0 * a + d0 * c) % p,
                      (c0 * b + d0 * dd) % p]).astype(np.int64)
        if kind == 'pgl':
            e = normalize(e, p)
        cc = ((e[0] * p + e[1]) * p + e[2]) * p + e[3]
        MT[g] = idx[cc]
    e_idx = int(idx[p ** 3 + 1])  # identity matrix (1,0,0,1)
    inv = np.argmax(MT == e_idx, axis=1).astype(np.int64)
    return N, MT, inv


def random_metacyclic(rng, lo, hi):
    """A random non-abelian metacyclic group Z_m x| Z_k with lo <= m*k <= hi, or None if sampling fails."""
    for _ in range(500):
        N = int(rng.integers(lo, hi + 1))
        divs = [m for m in range(3, N // 2 + 1) if N % m == 0]
        if not divs:
            continue
        m = divs[int(rng.integers(len(divs)))]
        k = N // m
        r = int(rng.integers(2, m))
        if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return group_table(m, k, r)
    return None


# ------------------------------------------------------------------------ search

def cost(MT, inv, N, S):
    """Uncovered elements in (S^-1 S)^2 and (S S^-1)^2 (0 means the Haar graph has diameter <= 5)."""
    Sinv = inv[S]
    X = np.unique(MT[Sinv[:, None], S[None, :]])
    Y = np.unique(MT[S[:, None], Sinv[None, :]])
    m1 = np.zeros(N, dtype=bool)
    m1[MT[np.ix_(X, X)]] = True
    m2 = np.zeros(N, dtype=bool)
    m2[MT[np.ix_(Y, Y)]] = True
    return 2 * N - int(m1.sum()) - int(m2.sum())


def anneal(MT, inv, N, d, rng, deadline):
    """Anneal a connection set until cost 0 or the deadline.  Returns S (int64 array) or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cost(MT, inv, N, S)
    best_c = cur
    stall = 0
    while True:
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            return None
        for _ in range(100):
            i = int(rng.integers(d))
            t = int(rng.integers(N))
            if np.any(S == t):
                continue
            old = int(S[i])
            S[i] = t
            c = cost(MT, inv, N, S)
            if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
                cur = c
                if cur == 0:
                    return S
                stall += 1
                if cur < best_c:
                    best_c = cur
                    stall = 0
            else:
                S[i] = old
                stall += 1
        if stall > STALL_LIMIT:
            S = rng.choice(N, d, replace=False).astype(np.int64)
            cur = cost(MT, inv, N, S)
            best_c = cur
            stall = 0


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N+g; edge A_g ~ B_{s*g} for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        row = MT[s].astype(np.int64)
        edges.extend(zip(ar.tolist(), (N + row).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        _, MT, _ = group_table(m, k, r)
        n, e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    mat_cache = {}
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1  # group order must exceed best_n / 2 to improve
        try:
            if rng.random() < 0.5:
                kind = 'pgl' if rng.random() < 0.5 else 'sl'
                if kind not in mat_cache:
                    mat_cache[kind] = matrix_group(13, kind)
                N, MT, inv = mat_cache[kind]
                if N < lo:
                    continue
            else:
                g = random_metacyclic(rng, max(lo, 1792), 2400)
                if g is None:
                    continue
                N, MT, inv = g
                if N < lo:
                    continue
            slice_end = min(deadline, time.monotonic() + SLICE)
            S = anneal(MT, inv, N, d, rng, slice_end)
            if S is not None:
                n, e = haar_edges(MT, S, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
