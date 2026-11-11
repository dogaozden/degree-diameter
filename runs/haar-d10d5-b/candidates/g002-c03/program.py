"""Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a finite group G of order N (metacyclic Z_m x| Z_k, non-abelian) and a connection set S of
10 distinct elements.  Vertices A_g = g and B_g = N + g.  Edges A_g ~ B_{s*g} for s in S.  This graph is
bipartite, 10-regular, and has 2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  For each candidate group of order N in [2001, 2060], run simulated annealing on S.  Cost is the number
of uncovered elements in the two conditions above, so cost 0 means a valid graph.  Moves replace one element of
S with a new element.  Several groups run round-robin in slots, and a slot restarts when it stalls.  Any
zero-cost configuration is checked with lib.is_valid before it is accepted.

SAFETY.  A valid Haar graph on 3582 vertices (the parent's group, Z_199 x| Z_9) is the fallback.  The output is
never smaller than that fallback.  Every accepted graph passes lib.is_valid.
"""
import math
import time
from collections import deque

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
BLOCK = 200
STALE_LIMIT = 4000
TEMP = 0.6
NLO, NHI = 2001, 2060
NSLOTS = 6

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
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
    return MT, inv


def cost(MT, inv, S, N):
    """Uncovered elements for (S^-1 S)^2 and (S S^-1)^2.  Zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    P = np.unique(MT[Si[:, None], S[None, :]])
    mk = np.zeros(N, dtype=bool)
    mk[MT[P[:, None], P[None, :]].ravel()] = True
    c1 = N - int(np.count_nonzero(mk))
    R = np.unique(MT[S[:, None], Si[None, :]])
    mk2 = np.zeros(N, dtype=bool)
    mk2[MT[R[:, None], R[None, :]].ravel()] = True
    c2 = N - int(np.count_nonzero(mk2))
    return c1 + c2


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, edges (g, N + s*g) for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        edges.extend(zip(ar.tolist(), (N + MT[int(s)].astype(np.int64)).tolist()))
    return edges


def specs_in_range(lo, hi):
    """(m, k, r) with m*k in [lo, hi], non-abelian metacyclic: r != 1, gcd(r, m) = 1, r^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for m in range(2, N // 2 + 1):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((m, k, r))
    return out


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        N = m * k
        e = haar_edges(MT, FALLBACK_S, N)
        if lib.is_valid(2 * N, e, d, D):
            best_n, best_edges = 2 * N, e
    except Exception:
        pass

    specs = specs_in_range(NLO, NHI)
    if not specs:
        return trivial(d, D) if best_edges is None else (best_n, best_edges)
    perm = rng.permutation(len(specs))
    queue = deque(specs[i] for i in perm)

    def new_slot():
        while queue:
            m, k, r = queue.popleft()
            N = m * k
            if 2 * N <= best_n:
                continue
            try:
                MT, inv = group_table(m, k, r)
            except Exception:
                continue
            S = rng.choice(N, d, replace=False).astype(np.int64)
            cur = cost(MT, inv, S, N)
            return {'N': N, 'MT': MT, 'inv': inv, 'S': S, 'cur': cur,
                    'best': cur, 'stale': 0}
        return None

    def run_block(sl):
        """Run BLOCK annealing steps on a slot.  Returns True if a zero-cost set was found."""
        N, MT, inv = sl['N'], sl['MT'], sl['inv']
        S = sl['S']
        for _ in range(BLOCK):
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if g in S:
                continue
            old = int(S[i])
            S[i] = g
            c = cost(MT, inv, S, N)
            if c <= sl['cur'] or rng.random() < math.exp(-(c - sl['cur']) / TEMP):
                sl['cur'] = c
                if c == 0:
                    return True
            else:
                S[i] = old
            if sl['cur'] < sl['best']:
                sl['best'] = sl['cur']
                sl['stale'] = 0
            else:
                sl['stale'] += 1
            if sl['stale'] > STALE_LIMIT:
                sl['S'] = rng.choice(N, d, replace=False).astype(np.int64)
                S = sl['S']
                sl['cur'] = cost(MT, inv, S, N)
                sl['best'] = sl['cur']
                sl['stale'] = 0
        return False

    slots = [new_slot() for _ in range(NSLOTS)]
    slots = [s for s in slots if s is not None]

    while time.monotonic() < deadline and slots:
        for idx in range(len(slots)):
            if time.monotonic() >= deadline:
                break
            sl = slots[idx]
            if sl is None:
                continue
            if 2 * sl['N'] <= best_n:
                slots[idx] = new_slot()
                continue
            if run_block(sl):
                N = sl['N']
                try:
                    e = haar_edges(sl['MT'], sl['S'], N)
                    ok = lib.is_valid(2 * N, e, d, D)
                except Exception:
                    ok = False
                if ok and 2 * N > best_n:
                    best_n, best_edges = 2 * N, e
                slots[idx] = new_slot()
        slots = [s for s in slots if s is not None]

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
