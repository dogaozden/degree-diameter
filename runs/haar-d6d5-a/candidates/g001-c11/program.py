"""Voltage lifts over small non-abelian groups, with a 2t-vertex base graph (t = 2 or 3).

Base multigraph: A_0..A_{t-1} and B_0..B_{t-1}, with a dart pattern pat[i][j] = number of edges between A_i and B_j.
Every A_i and every B_j has total degree 6.  Lift over a group G of order N: vertices (X, x) for x in G, and
edges (A_i, x) ~ (B_j, x*v) for each dart (i, j, v).  The voltages v into each (i, j) are distinct, so the lift
is simple.  Left multiplication by any h in G is an automorphism, so the eccentricity of (X, x) equals that of
(X, e).  The diameter is therefore at most 5 iff the 2t representatives (X, e) all reach every vertex within 5
steps.  That gives a cheap numpy cost (unreached pairs).  Annealing over voltages drives the cost to 0.

Each group/pattern entry is searched in increasing order of vertex count.  Every candidate is checked with
lib.is_valid before it is kept.  If nothing valid beats the fallback, the parent's valid Haar graph (660) is used.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DIAM = 5
DEG = 6

# Dart patterns for a base with t vertices per side: every row and column sums to DEG.
PATTERNS = {
    2: [[[3, 3], [3, 3]], [[4, 2], [2, 4]], [[5, 1], [1, 5]]],
    3: [[[3, 2, 1], [1, 3, 2], [2, 1, 3]], [[2, 2, 2], [2, 2, 2], [2, 2, 2]]],
}

FALLBACK_GROUP = (33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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


# ------------------------------------------------------------------------- Haar fallback

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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------- voltage lifts

def lift_nbr(MT, inv, t, V):
    """Neighbour array (2*t*N, DEG).  A_i-vertex x is i*N + x, B_j-vertex y is (t+j)*N + y."""
    N = MT.shape[0]
    X = np.arange(N)
    blocks = []
    for i in range(t):
        cols = []
        for j in range(t):
            for v in V[i][j]:
                cols.append((t + j) * N + MT[X, v].astype(np.int64))
        blocks.append(np.stack(cols, axis=1))
    for j in range(t):
        cols = []
        for i in range(t):
            for v in V[i][j]:
                cols.append(i * N + MT[X, inv[v]].astype(np.int64))
        blocks.append(np.stack(cols, axis=1))
    return np.concatenate(blocks, axis=0)


def lift_cost(nbr, t, D):
    """Number of (orbit representative, vertex) pairs at distance more than D.  0 means diameter <= D."""
    nt = nbr.shape[0]
    orbits = 2 * t
    N = nt // orbits
    reach = np.zeros((orbits, nt), dtype=bool)
    reach[np.arange(orbits), np.arange(orbits) * N] = True
    for _ in range(D):
        reach = reach | reach[:, nbr].any(axis=2)
    return orbits * nt - int(np.count_nonzero(reach))


def _random_state(t, pat, N, rng):
    return [[[int(v) for v in rng.choice(N, size=pat[i][j], replace=False)] if pat[i][j] else []
             for j in range(t)] for i in range(t)]


def _propose(V, cells, t, N, rng):
    i, j = cells[int(rng.integers(len(cells)))]
    k = int(rng.integers(len(V[i][j])))
    while True:
        v = int(rng.integers(N))
        if v not in V[i][j]:
            break
    W = [[list(V[a][b]) for b in range(t)] for a in range(t)]
    W[i][j][k] = v
    return W


def _cost(MT, inv, t, V, D):
    return lift_cost(lift_nbr(MT, inv, t, V), t, D)


def anneal(MT, inv, t, pat, deadline, rng, D=DIAM):
    """Metropolis search over voltages.  Returns voltage state with cost 0, or None."""
    N = MT.shape[0]
    cells = [(i, j) for i in range(t) for j in range(t) if pat[i][j]]
    V = _random_state(t, pat, N, rng)
    cur = _cost(MT, inv, t, V, D)
    best_c, best_V = cur, V
    since = 0
    while best_c > 0 and time.monotonic() < deadline:
        cands = []
        for _ in range(4):
            W = _propose(V, cells, t, N, rng)
            cands.append((_cost(MT, inv, t, W, D), W))
        c, W = min(cands, key=lambda x: x[0])
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / 0.8):
            V, cur = W, c
        if cur < best_c:
            best_c, best_V, since = cur, V, 0
        else:
            since += 1
        if since > 400:
            V = _random_state(t, pat, N, rng)
            cur = _cost(MT, inv, t, V, D)
            since = 0
    return best_V if best_c == 0 else None


def _edges(nbr):
    nt = nbr.shape[0]
    return nt, [(u, int(w)) for u in range(nt // 2) for w in nbr[u]]


# ------------------------------------------------------------------------------ schedule

def build_entries(rng):
    """(vertex count, t, pattern, (m, k, lam)) for orders that would beat the record."""
    entries = []
    for t, Ns in ((2, range(166, 176)), (3, range(111, 119))):
        for N in Ns:
            cands = []
            for k in range(2, N):
                if N % k == 0 and N // k >= 3:
                    m = N // k
                    for lam in range(2, m):
                        if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                            cands.append((m, k, lam))
            group = cands[int(rng.integers(len(cands)))] if cands else (N, 1, 1)
            pats = PATTERNS[t]
            pat = pats[int(rng.integers(len(pats)))]
            entries.append((2 * t * N, t, pat, group))
    entries.sort(key=lambda e: e[0])
    return entries


def search_lifts(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    entries = build_entries(rng)
    best = None
    for idx, (_, t, pat, (m, k, lam)) in enumerate(entries):
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.2:
            break
        slice_t = remaining / (len(entries) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            V = anneal(MT, inv, t, pat, now + slice_t, rng, D)
        except Exception:
            continue
        if V is None:
            continue
        try:
            n, edges = _edges(lift_nbr(MT, inv, t, V))
            if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            continue
    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = search_lifts(d, D, seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
