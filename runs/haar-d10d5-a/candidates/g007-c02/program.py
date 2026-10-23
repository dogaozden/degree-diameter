"""Two-orbit voltage lift search for the d=10, D=5 bipartite degree-diameter case.

Construction: a bipartite lift of a 2+2 base multigraph over a metacyclic group G of order N,
with 4N vertices. A-vertices (i, g) and B-vertices (j, h), i, j in {0, 1}. Each A-vertex row i has
5 darts to B_0 and 5 darts to B_1, so every vertex has degree 10. Dart (i, j, s) joins (i, g) to
(j, s*g). The 20 voltages are searched by hill climbing on the number of ordered vertex pairs at
distance more than 5. A graph is returned only if lib.is_valid accepts it. Otherwise the code falls
back to a valid smaller Haar graph, and then to a trivial graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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


# ------------------------------------------------------------------ two-orbit lift search

def make_nbr(MT, inv, V, N):
    """Neighbour array (4N x 10). A-vertex (i, g) = i*N+g, B-vertex (j, h) = 2N + j*N + h."""
    nbr = np.empty((4 * N, 10), dtype=np.int64)
    g = np.arange(N)
    for i in range(2):
        for j in range(2):
            for t in range(5):
                s = int(V[i, j, t])
                # A-side: (i, g) ~ (j, s*g)
                nbr[i * N + g, j * 5 + t] = 2 * N + j * N + MT[s, g]
                # B-side: (j, h) ~ (i, s^-1 h)
                nbr[2 * N + j * N + g, i * 5 + t] = i * N + MT[int(inv[s]), g]
    return nbr


def unreached(nbr, n, D=5):
    """Number of ordered vertex pairs at distance more than D (0 iff diameter <= D)."""
    nb = nbr.tolist()
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def lift_specs(rng):
    """Metacyclic groups of order N in [1001, 1060] (so 4N > 4000), two non-trivial lam each, shuffled."""
    out = []
    for N in range(1001, 1061):
        for k in range(2, 11):
            if N % k:
                continue
            m = N // k
            cnt = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    cnt += 1
                    if cnt >= 2:
                        break
    if not out:
        return out
    perm = rng.permutation(len(out))
    return [out[i] for i in perm]


def lift_search(d, D, rng, deadline):
    """Hill-climb the voltages over several groups. Return (n, edges) if a valid graph is found, else None."""
    for m, k, lam in lift_specs(rng):
        if time.monotonic() >= deadline:
            break
        N = m * k
        MT, inv = group_meta(m, k, lam)
        V = np.zeros((2, 2, 5), dtype=np.int64)
        for i in range(2):
            for j in range(2):
                V[i, j] = rng.choice(N, 5, replace=False)
        cur = unreached(make_nbr(MT, inv, V, N), 4 * N, D)
        stall = 0
        while cur > 0 and time.monotonic() < deadline and stall < 300:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            t = int(rng.integers(5))
            x = int(rng.integers(N))
            if np.any(V[i, j] == x):
                continue
            old = int(V[i, j, t])
            V[i, j, t] = x
            c = unreached(make_nbr(MT, inv, V, N), 4 * N, D)
            if c <= cur or rng.random() < 0.03:
                if c < cur:
                    stall = 0
                else:
                    stall += 1
                cur = c
            else:
                V[i, j, t] = old
                stall += 1
        if cur == 0:
            nbr = make_nbr(MT, inv, V, N)
            nb = nbr[:2 * N].tolist()
            edges = [(a, b) for a in range(2 * N) for b in nb[a]]
            n = 4 * N
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# ------------------------------------------------------------------------- trivial graphs

def trivial(d, D):
    """Always-valid small graph for any (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2 and d >= 1:
        # K_{d,d}: bipartite, degree d, diameter 2
        n = 2 * d
        edges = [(i, d + j) for i in range(d) for j in range(d)]
        return n, edges
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


# ----------------------------------------------------------------------------------- build

FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)

    try:
        res = lift_search(d, D, rng, deadline)
    except Exception:
        res = None
    if res is not None:
        return res

    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked_haar(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != (10, 5):
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
