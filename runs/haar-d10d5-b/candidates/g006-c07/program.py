"""Haar-graph search with an exact word-cover cost (d=10, D=5).

NEW HELPER (not in the parent): an exact, vectorised cover cost for Haar graphs.
For a connection set S in a group G (table MT, inverse vector inv), the Haar graph
with vertices (g,A)~(s*g,B) has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
cover_cost(S) returns |G \\ (S^-1 S)^2| + |G \\ (S S^-1)^2| using one np.unique on
at most d+1 elements and one bincount over at most (d^2+1)^2 products per side, so
each annealing move costs roughly 100 microseconds. Cost 0 means a valid graph.

SEARCH.  Several annealers run round-robin, each on its own metacyclic group Z_m x|_r Z_k
of order N slightly above the current threshold best_n/2.  Every zero-cost set is turned
into a Haar graph (2N vertices, d-regular, bipartite) and verified with lib.is_valid
before it is accepted.  The validated Haar fallback from the parent (1791 elements,
3582 vertices) is kept as the floor, so the output is never worse than the parent.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 5
ANNEAL_LEN = 3000

# Valid Haar fallback from the parent (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv) where MT[x, y] = x*y and inv[x] is the inverse of x.
    """
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


def metacyclic_options(N):
    """All non-abelian metacyclic presentations (m, k, r) with m*k = N, r != 1, r^k = 1 mod m."""
    opts = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


# ------------------------------------------------------------------------------ new helper

def cover_cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus those of (S S^-1)^2 (zero iff diameter <= 5)."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    A = np.unique(MT[iS[:, None], Sa[None, :]])        # s^-1 t
    P = MT[A[:, None], A[None, :]]                     # (s^-1 t)(u^-1 v)
    c = N - int(np.count_nonzero(np.bincount(P.ravel(), minlength=N)))
    B = np.unique(MT[Sa[:, None], iS[None, :]])        # s t^-1
    Q = MT[B[:, None], B[None, :]]
    c += N - int(np.count_nonzero(np.bincount(Q.ravel(), minlength=N)))
    return c


def haar_anneal(MT, inv, N, d, rng):
    """Generator: one annealing move per yield. Yields ('found', S) at cost 0, then ends."""
    while True:
        S = [int(x) for x in rng.choice(N, d, replace=False)]
        cur = cover_cost(MT, inv, S, N)
        for step in range(ANNEAL_LEN):
            if cur == 0:
                yield ('found', list(S))
                return
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if g in S:
                yield None
                continue
            old = S[i]
            S[i] = g
            c = cover_cost(MT, inv, S, N)
            temp = 0.1 + 1.2 * (1.0 - step / ANNEAL_LEN)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                S[i] = old
            yield None
        # restart from a fresh random set when stuck


def spawn(lo, hi, d, rng):
    """A fresh annealing task on a random non-abelian metacyclic group with order in [lo, hi]."""
    for _ in range(50):
        N = int(rng.integers(lo, hi + 1))
        opts = metacyclic_options(N)
        if opts:
            m, k, r = opts[int(rng.integers(len(opts)))]
            MT, inv = group_table(m, k, r)
            gen = haar_anneal(MT, inv, N, d, rng)
            return {'gen': gen, 'N': N, 'MT': MT}
    return None


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g (= g) joins B-vertex N + s*g for each s in S."""
    edges = []
    for s in S:
        ys = (N + MT[int(s)].astype(np.int64)).tolist()
        edges.extend(zip(range(N), ys))
    return edges


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        e = haar_edges(MT, FALLBACK_S, m * k)
        n = 2 * m * k
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    def window():
        lo = best_n // 2 + 1
        return lo, lo + 300

    pool = []
    for _ in range(POOL):
        lo, hi = window()
        pool.append(spawn(lo, hi, d, rng))

    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task is None or 2 * task['N'] <= best_n:
                lo, hi = window()
                pool[idx] = spawn(lo, hi, d, rng)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                lo, hi = window()
                pool[idx] = spawn(lo, hi, d, rng)
                continue
            if out is not None:
                N = task['N']
                n = 2 * N
                try:
                    edges = haar_edges(task['MT'], out[1], N)
                    ok = n > best_n and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best_edges = n, edges
                lo, hi = window()
                pool[idx] = spawn(lo, hi, d, rng)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
