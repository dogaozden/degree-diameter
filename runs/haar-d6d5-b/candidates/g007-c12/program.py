"""Voltage-lift search for d=6, D=5 (a different construction from the Haar search), with a verified Haar fallback.

CONSTRUCTION.  Base multigraph: 2 A-vertices and 2 B-vertices.  A-vertex i and B-vertex j are joined by
M[i][j] darts, each with a voltage g in a finite group G of order N.  The lift has vertices (u, x), u in
{A0, A1, B0, B1}, x in G, and edges (A_i, x) ~ (B_j, x*g) for every dart (i, j, g).  Left multiplication
x -> h*x is an automorphism, so the four fibres are each transitive and the diameter check only needs one
BFS source per base vertex (4 BFS runs).  With M having row and column sums 6, the lift is 6-regular and
bipartite on 4N vertices.  N = 172..180 gives 688..720 vertices, above the record 684.

SEARCH.  Simulated annealing over the voltages, minimising the number of vertices farther than D from the
four sources.  Cost 0 means the lift has diameter <= D.  Every candidate is checked with lib.is_valid before
it is returned.

FALLBACK.  The verified 660-vertex Haar graph from the parent program, returned if the search finds nothing.
"""
import math
import random
import time
from collections import deque

import numpy as np

import lib

TARGET = (6, 5)

# Base multiplicity matrices M[i][j] = number of darts from A_i to B_j.  Row and column sums are all 6.
MULTS = [
    ((3, 3), (3, 3)),
    ((4, 2), (2, 4)),
    ((2, 4), (4, 2)),
    ((5, 1), (1, 5)),
]


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
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


def lift_groups(lo, hi):
    """Metacyclic Z_m x|_lam Z_k (lam != 1, so non-abelian) with lo <= m*k <= hi, sorted by order."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
    return out


# ------------------------------------------------------------------------------------- lift machinery

def lift_cost(N, cols, volt, D):
    """Total number of vertices farther than D (or unreachable) from the four base sources.
    cols[g][x] = x*g.  volt maps (i, j) to a list of voltages."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for (i, j), gs in volt.items():
        for g in gs:
            cg = cols[g]
            for x in range(N):
                a = i * N + x
                b = (2 + j) * N + cg[x]
                adj[a].append(b)
                adj[b].append(a)
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        dist = [-1] * V
        dist[s] = 0
        seen = 1
        q = deque([s])
        while q:
            v = q.popleft()
            dv = dist[v]
            if dv == D:
                continue
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dv + 1
                    seen += 1
                    q.append(w)
        total += V - seen
    return total


def lift_edges(N, cols, volt):
    edges = []
    for (i, j), gs in volt.items():
        for g in gs:
            cg = cols[g]
            for x in range(N):
                edges.append((i * N + x, (2 + j) * N + cg[x]))
    return 4 * N, edges


def anneal(N, cols, mult, D, end, rnd):
    """Anneal voltages for one base multiplicity pattern until cost 0 or time runs out.
    Returns (best cost, best voltages)."""
    keys = [(i, j) for i in range(2) for j in range(2) if mult[i][j] > 0]
    volt = {(i, j): rnd.sample(range(N), mult[i][j]) for (i, j) in keys}
    cur = lift_cost(N, cols, volt, D)
    best = cur
    bestv = {k: list(v) for k, v in volt.items()}
    T = 0.7
    while cur > 0 and time.monotonic() < end:
        key = rnd.choice(keys)
        lst = volt[key]
        idx = rnd.randrange(len(lst))
        new = rnd.randrange(N)
        if new in lst:
            continue
        old = lst[idx]
        lst[idx] = new
        c = lift_cost(N, cols, volt, D)
        if c <= cur or rnd.random() < math.exp(-(c - cur) / T):
            cur = c
            if c < best:
                best = c
                bestv = {k: list(v) for k, v in volt.items()}
        else:
            lst[idx] = old
    return best, bestv


# ------------------------------------------------------------------------------------ fallbacks

def haar_checked(MT, S, d, D):
    """Verified Haar graph on (g, A) ~ (s*g, B) for s in S, or None."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = min(0.75 * time_limit, time_limit - 8.0)
    deadline = t0 + budget
    rnd = random.Random(seed)

    groups = lift_groups(172, 180)[:8]
    group_cache = {}

    def cols_for(gp):
        if gp not in group_cache:
            m, k, lam = gp
            MT, _ = group_meta(m, k, lam)
            N = MT.shape[0]
            group_cache[gp] = (N, MT.T.tolist())
        return group_cache[gp]

    combos = [(gp, mult) for gp in groups for mult in MULTS[:2]]
    slice_len = 4.0

    while time.monotonic() < deadline and combos:
        for gp, mult in combos:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_len)
            try:
                N, cols = cols_for(gp)
                c, volt = anneal(N, cols, mult, D, end, rnd)
            except Exception:
                continue
            if c == 0:
                n, edges = lift_edges(N, cols, volt)
                if lib.is_valid(n, edges, d, D):
                    return n, edges

    # Fallback: verified Haar graph on 660 vertices.
    try:
        MT, _ = FALLBACK[0]()
        g = haar_checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
