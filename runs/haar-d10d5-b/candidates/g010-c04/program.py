"""Bold variant for the d=10, D=5 target: 4-fibre voltage lifts instead of Haar graphs.

CONSTRUCTION.  Take a group G of order N and a base bipartite multigraph on two A-fibres {A0, A1} and two
B-fibres {B0, B1}.  Dart (i, j, g) joins (x, A_i) to (x*g, B_j) for all x in G.  With c darts A0-B0,
10-c darts A0-B1, 10-c darts A1-B0 and c darts A1-B1, every vertex has degree exactly 10 when the darts
between each fibre pair have distinct voltages.  The graph has 4N vertices and is bipartite and simple.
Left multiplication by h in G is an automorphism that is transitive on each fibre, so the diameter is at
most 5 iff the four fibre representatives (identity in each fibre) have eccentricity at most 5.

SEARCH.  Binary search on N in a window around 900..1010 (4N vertices).  For each N, simulated annealing
over the voltages and random metacyclic groups of order N.  The cost is the number of vertices left unreached
within distance 5 from the four representatives.  A candidate is only returned after lib.is_valid accepts it.

SAFETY.  The parent's valid Haar graph (3582 vertices) is checked first and kept as the default answer.
Any case other than (10, 5) returns a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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


def group_options(N):
    """All metacyclic groups Z_m x|_lam Z_k of order N (k = 1 is the cyclic group)."""
    opts = [(N, 1, 1)]
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                opts.append((m, k, lam))
    return opts


# -------------------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def haar_fallback():
    """A valid Haar graph (2 * 1791 = 3582 vertices), verified by the caller."""
    MT, _ = group_meta(199, 9, 180)
    S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
    return haar_edges(MT, S)


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- 4-fibre lift search

def build_adj(MTT, inv, V, N):
    """Adjacency array (4N x 10).  Fibre f occupies rows f*N..f*N+N-1; fibres 0,1 are A, fibres 2,3 are B."""
    ADJ = np.empty((4 * N, 10), dtype=np.int64)
    for i in (0, 1):
        col = 0
        for j in (0, 1):
            for g in V[i][j]:
                ADJ[i * N:(i + 1) * N, col] = (2 + j) * N + MTT[g]
                col += 1
    colB = [0, 0]
    for i in (0, 1):
        for j in (0, 1):
            for g in V[i][j]:
                ADJ[(2 + j) * N:(3 + j) * N, colB[j]] = i * N + MTT[inv[g]]
                colB[j] += 1
    return ADJ


def unreached(ADJ, N, sources):
    """Total number of vertices not within distance 5 of each source (0 means diameter <= 5)."""
    T = 4 * N
    tot = 0
    for s in sources:
        R = np.zeros(T, dtype=bool)
        R[s] = True
        F = np.array([s], dtype=np.int64)
        for _ in range(5):
            new = np.zeros(T, dtype=bool)
            new[ADJ[F].ravel()] = True
            new &= ~R
            if not new.any():
                break
            R |= new
            F = np.flatnonzero(new)
        tot += T - int(np.count_nonzero(R))
    return tot


def lift_edges(MTT, N, V):
    """Edge list of the 4-fibre lift: returns (n, edges)."""
    edges = []
    base = np.arange(N, dtype=np.int64)
    for i in (0, 1):
        for j in (0, 1):
            for g in V[i][j]:
                us = (i * N + base).tolist()
                vs = ((2 + j) * N + MTT[g].astype(np.int64)).tolist()
                edges.extend(zip(us, vs))
    return 4 * N, edges


PATIENCE = 1500
TEMP = 1.0


def search_lift(N, deadline, rng):
    """Anneal voltages for a 4-fibre lift of order N until cost 0 (verified) or the deadline.  Returns (n, edges) or None."""
    opts = group_options(N)
    while time.monotonic() < deadline:
        m, k, lam = opts[int(rng.integers(len(opts)))]
        MT, inv = group_meta(m, k, lam)
        MTT = np.ascontiguousarray(MT.T)
        c = int(rng.choice([4, 5, 6]))
        cnt = [[c, 10 - c], [10 - c, c]]
        V = [[rng.choice(N, cnt[i][j], replace=False).astype(np.int64) for j in (0, 1)] for i in (0, 1)]
        sources = [0, N, 2 * N, 3 * N]

        def cost():
            return unreached(build_adj(MTT, inv, V, N), N, sources)

        cur = cost()
        stale = 0
        while cur > 0 and stale < PATIENCE and time.monotonic() < deadline:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            s = int(rng.integers(cnt[i][j]))
            g = int(rng.integers(N))
            if g in V[i][j]:
                continue
            old = V[i][j][s]
            V[i][j][s] = g
            new = cost()
            d = new - cur
            if d <= 0 or rng.random() < math.exp(-d / TEMP):
                stale = 0 if d < 0 else stale + 1
                cur = new
            else:
                V[i][j][s] = old
                stale += 1
        if cur == 0:
            n, edges = lift_edges(MTT, N, V)
            if lib.is_valid(n, edges, 10, 5):
                return n, edges
    return None


# --------------------------------------------------------------------------------------------- build

TARGET = (10, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.72 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        best = None

    lo, hi = 895, 1010   # lo: assumed-achievable N (4*895 = 3580 < 3582), hi: upper probe bound
    while lo < hi:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 2.0:
            break
        mid = (lo + hi + 1) // 2
        slice_end = min(deadline, now + max(3.0, 0.45 * remaining))
        try:
            res = search_lift(mid, slice_end, rng)
        except Exception:
            res = None
        if res is not None:
            if best is None or res[0] > best[0]:
                best = res
            lo = mid
        else:
            hi = mid - 1

    if best is None:
        return trivial(d, D)
    return best
