"""Multi-vertex voltage lifts for the bipartite degree-diameter problem (diameter 5, d = 10).

THEORY.  Take a bipartite base graph with k A-vertices and k B-vertices, where each vertex has d darts (a dart
is an edge of the base graph carrying a voltage from a finite group G of order N).  Its lift has 2kN vertices:
fibre u consists of vertices (u, x) for x in G, and dart (i, j, g) joins (i, x) to (k+j, x*g).  The lift is
bipartite and has max degree d.

Left multiplication by h, x -> h*x, is an automorphism of the lift, so it is transitive on every fibre.  Hence
the diameter is at most D iff the ball of radius D around each of the 2k fibre identities (u, e) covers the whole
graph.  That check takes only 2k BFS-like passes, done here with bitmasks over the sources.  The cost is the
number of (source, vertex) pairs left uncovered, and cost 0 means the lift is valid.

PROCEDURE.  Metacyclic groups Z_m x| Z_k2 are chosen with 2kN just above 4000.  For each group, a local search
over the k*d voltages minimises the cost.  A zero-cost lift is rebuilt as an explicit edge list and checked with
lib.is_valid.  If no lift succeeds in the budget, the precomputed valid Haar graph (3582 vertices) is returned,
checked at run time.  Other (d, D) cases get a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with index a*k + j for (a, j), (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def metacyclic_groups(N):
    """Up to two (m, k2, lam) with m*k2 = N, m >= 3, lam^k2 = 1 mod m and lam != 1 (larger k2 first)."""
    found = []
    for k2 in range(2, N + 1):
        if N % k2 or N // k2 < 3:
            continue
        m = N // k2
        for a in range(2, min(m, 400)):
            if pow(a, k2, m) == 1:
                found.append((m, k2, a))
                break
    found.sort(key=lambda t: -t[1])
    return found[:2]


def lift_tasks():
    """Candidate (V, k, m, k2, lam) with V = 2kN > 4000, ordered by V, at most 12 entries."""
    tasks = []
    for k in (2, 3, 4, 5):
        Nmin = 4000 // (2 * k) + 1
        for N in range(Nmin, Nmin + 20):
            for (m, k2, lam) in metacyclic_groups(N):
                tasks.append((2 * k * N, k, m, k2, lam))
    tasks.sort()
    return tasks[:12]


# ----------------------------------------------------------------------------- lift search

def lift_search(MT, inv, k, d, D, deadline, rng):
    """Anneal the k*d voltages of a lift of a base with shifts c_r; return (c, g) with cost 0, or None."""
    N = MT.shape[0]
    V = 2 * k * N
    ar = np.arange(N)
    c = rng.integers(0, k, size=d)
    src = np.arange(2 * k) * N
    bits = (np.int64(1) << np.arange(2 * k, dtype=np.int64))
    shifts = np.arange(2 * k, dtype=np.int64)

    def build_nb(g):
        nb = np.empty((V, d), dtype=np.int64)
        for i in range(k):
            for r in range(d):
                j = (i + int(c[r])) % k
                gi = int(g[i, r])
                nb[i * N:(i + 1) * N, r] = (k + j) * N + MT[ar, gi]
                nb[(k + j) * N:(k + j + 1) * N, r] = i * N + MT[ar, int(inv[gi])]
        return nb

    def cost(nb):
        M = np.zeros(V, dtype=np.int64)
        M[src] = bits
        for _ in range(D):
            M = M | np.bitwise_or.reduce(M[nb], axis=1)
        cnt = ((M[:, None] >> shifts) & 1).sum(axis=0)
        return int((V - cnt).sum())

    g = rng.integers(0, N, size=(k, d)).astype(np.int64)
    cur = cost(build_nb(g))
    T, since, patience = 0.5, 0, 3000
    while cur > 0 and time.monotonic() < deadline:
        if since > patience:
            g = rng.integers(0, N, size=(k, d)).astype(np.int64)
            cur = cost(build_nb(g))
            since = 0
            continue
        i = int(rng.integers(k))
        r = int(rng.integers(d))
        old = int(g[i, r])
        g[i, r] = int(rng.integers(N))
        new = cost(build_nb(g))
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            since = 0 if delta < 0 else since + 1
        else:
            g[i, r] = old
            since += 1
    if cur == 0:
        return c.copy(), g.copy()
    return None


def lift_graph(MT, k, c, g, d):
    """Edge list of the lift: A-vertex (i, x) = i*N + x, B-vertex (j, y) = (k+j)*N + y."""
    N = MT.shape[0]
    ar = np.arange(N)
    edges = set()
    for i in range(k):
        for r in range(d):
            j = (i + int(c[r])) % k
            tgt = MT[ar, int(g[i, r])]
            for x in range(N):
                edges.add((i * N + x, (k + j) * N + int(tgt[x])))
    return 2 * k * N, sorted(edges)


# ----------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    gg = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(gg, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# ----------------------------------------------------------------------------- driver

def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    tasks = lift_tasks()
    for idx, (V, k, m, k2, lam) in enumerate(tasks):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(tasks) - idx)
        try:
            MT, inv = group_meta(m, k2, lam)
            found = lift_search(MT, inv, k, d, D, end, rng)
            if found is not None:
                c, g = found
                n, edges = lift_graph(MT, k, c, g, d)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            continue
    try:
        MT, inv = FALLBACK[0]()
        r = checked(MT, FALLBACK[1], d, D)
        if r is not None:
            return r
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
