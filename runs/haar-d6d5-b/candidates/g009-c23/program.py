"""Multi-orbit voltage-lift search for the bipartite degree-diameter problem (d=6, D=5), with a Haar fallback.

CONSTRUCTION.  Take a finite group G of order N (metacyclic Z_m x| Z_k, nonabelian) and a 2+2 base
multigraph: A_0, A_1 on one side and B_0, B_1 on the other.  The base is given by a 2x2 matrix n_ij of
darts with row and column sums 6, so the base is 6-regular.  Each dart (i, j, g) joins (A_i, x) to
(B_j, x*g) for every x in G.  The lift has 4N vertices, is bipartite and 6-regular, and has diameter at
most 5 exactly when the search finds a valid voltage assignment.  Orders N >= 172 give more than 684
vertices, which would beat the record.

SEARCH.  For each group, the 6 voltages are annealed against the objective lib.bad_pairs(n, edges, 5),
the number of vertex pairs at distance greater than 5.  Groups are visited round-robin, with random
restarts and random base matrices.  Any candidate with zero bad pairs is confirmed with lib.is_valid.

SAFETY.  If the search does not succeed in time, the proven Haar graph of order 660 (checked with
lib.is_valid) is returned.  Calibration and other cases return the original small valid graphs.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)


# ----------------------------------------------------------------------- group table

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with element (a, j) -> index a*k + j, product (a,j)(b,l) = (a + lam^j b, j + l).
    Requires lam^k = 1 mod m.  Returns the multiplication table as an int64 numpy array."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return MT


def group_candidates(lo=172, hi=190, cap=24):
    """Nonabelian metacyclic groups Z_m x| Z_k of orders lo..hi, smallest orders first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                out.append((m, k, lam))
                break
    return out[:cap]


# ----------------------------------------------------------------- multi-orbit lift

MATS = [
    [[3, 3], [3, 3]],
    [[4, 2], [2, 4]],
    [[2, 4], [4, 2]],
    [[5, 1], [1, 5]],
]


def lift_graph(mt, N, pairs, gs):
    """Lift: dart t = (i, j) with voltage gs[t] joins (A_i, x) to (B_j, x * gs[t]) for all x in G.
    A_i vertex x is i*N + x; B_j vertex y is 2N + j*N + y."""
    E = set()
    for (i, j), g in zip(pairs, gs):
        ba = i * N
        bb = 2 * N + j * N
        for x in range(N):
            E.add((ba + x, bb + mt[x][g]))
    return 4 * N, list(E)


def search_group(mt, N, mat, deadline, rng, T=0.5, patience=2000):
    """Anneal the 6 voltages of a 2+2 base lift over one group.  Returns (voltages, cost, edges)."""
    pairs = [(i, j) for i in range(2) for j in range(2) for _ in range(mat[i][j])]
    dd = len(pairs)

    def random_voltages():
        return [int(x) for x in rng.integers(0, N, size=dd)]

    gs = random_voltages()
    n, E = lift_graph(mt, N, pairs, gs)
    cur = lib.bad_pairs(n, E, 5)
    best = (list(gs), cur, E)
    since = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return best
        t = int(rng.integers(dd))
        old = gs[t]
        gs[t] = int(rng.integers(N))
        n, E = lift_graph(mt, N, pairs, gs)
        c = lib.bad_pairs(n, E, 5)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if c < best[1]:
                best = (list(gs), c, E)
                since = 0
        else:
            gs[t] = old
        since += 1
        if since > patience:
            gs = random_voltages()
            n, E = lift_graph(mt, N, pairs, gs)
            cur = lib.bad_pairs(n, E, 5)
            since = 0
    return best


def multi_orbit_search(d, D, rng, deadline):
    """Round-robin over candidate groups and base matrices.  Returns a verified (n, edges) or None."""
    groups = group_candidates()
    if not groups:
        return None
    tables = {}
    gi = 0
    while time.monotonic() < deadline - 0.5:
        m, k, lam = groups[gi % len(groups)]
        gi += 1
        N = m * k
        if (m, k, lam) not in tables:
            tables[(m, k, lam)] = group_meta(m, k, lam).tolist()
        mt = tables[(m, k, lam)]
        mat = MATS[int(rng.integers(len(MATS)))]
        slice_end = min(deadline, time.monotonic() + 5.0)
        gs, c, E = search_group(mt, N, mat, slice_end, rng)
        if c == 0:
            n = 4 * N
            if lib.is_valid(n, E, d, D):
                return n, E
    return None


# -------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Haar graph of group table MT and connection set S: (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def fallback_graph(d, D):
    try:
        MT = group_meta(33, 10, 26)
        return checked_haar(MT, [0, 179, 116, 180, 47, 306], d, D)
    except Exception:
        return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------ entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.72 * time_limit, time_limit - 12.0))
    rng = np.random.default_rng(seed)
    res = None
    try:
        res = multi_orbit_search(d, D, rng, deadline)
    except Exception:
        res = None
    if res is not None:
        return res
    fb = fallback_graph(d, D)
    if fb is not None:
        return fb
    return trivial(d, D)
