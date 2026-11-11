"""Two-base-vertex group lifts for the bipartite degree-diameter problem, target d=6 D=5.

NEW CONSTRUCTION.  The parent used one A-class and one B-class (a Haar graph). This version uses two
A-classes and two B-classes over a group G of order N.  A-vertices (i, x) and B-vertices (j, y), with
i, j in {0, 1}, x, y in G.  A dart (i, j, s) joins (A_i, x) to (B_j, x*s).  Each A_i has six darts and each
B_j receives six darts, so the graph is 6-regular and bipartite on 4N vertices.  The dart multiplicities
follow a pattern a in {1, 2, 3}: m00 = m11 = a and m01 = m10 = 6 - a.  Left multiplication by G is an
automorphism, so every vertex of a class is equivalent to that class's representative.  The diameter is
therefore at most 5 iff a BFS of radius 5 from the four representatives reaches every vertex.  The order is
4N, so N >= 172 beats the record 684.

SEARCH.  Simulated annealing over the 12 dart group elements.  The cost is the number of unreached vertices
summed over the four sources.  Every candidate is checked with lib.is_valid before it is returned.  If nothing
is found, the parent's valid Haar graph is tried, and then a complete bipartite graph K_{d,d}.  The projective
plane is used for the D = 3 calibration case.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
D_TARGET = 5
NLO, NHI = 172, 200   # 4*N vertices; N = 172 gives 688 > 684


def _group_meta(m, k, lam):
    """Z_m x|_lam Z_k with element (a, j) stored as a*k + j; returns (MT, inv), identity = 0."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = (((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k
                     + (j[lo:hi, None] + j[None, :]) % k)
    MT = np.ascontiguousarray(MT)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


_GROUP_CACHE = {}


def _group(m, k, lam):
    key = (m, k, lam)
    if key not in _GROUP_CACHE:
        _GROUP_CACHE.clear()
        _GROUP_CACHE[key] = _group_meta(m, k, lam)
    return _GROUP_CACHE[key]


def _group_list(lo, hi):
    """One non-abelian metacyclic group Z_m x|_lam Z_k per (m, k) with lo <= m*k <= hi, smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    break
    return out


def _pattern(a):
    """Dart-to-B assignment: JA[i, c] is the B index of dart c at A_i; BL[j] lists (i, c) pairs for B_j."""
    JA = np.array([[0] * a + [1] * (6 - a), [0] * (6 - a) + [1] * a], dtype=np.int64)
    BL = []
    for j in (0, 1):
        ii, cc = np.nonzero(JA == j)
        BL.append((ii.astype(np.int64), cc.astype(np.int64)))
    return JA, BL


def _init_sv(N, JA, rng):
    """Random dart group elements, distinct within each (i, j) block."""
    sv = np.zeros((2, 6), dtype=np.int64)
    for i in (0, 1):
        for j in (0, 1):
            cols = np.nonzero(JA[i] == j)[0]
            sv[i, cols] = rng.choice(N, size=len(cols), replace=False)
    return sv


def _build_nbr(MT, inv, sv, JA, BL, N):
    """Neighbour table (4N x 6). Rows 0..2N-1 are A-vertices (i*N + x), rows 2N..4N-1 are B-vertices (2N + j*N + y)."""
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        nbr[i * N:(i + 1) * N] = 2 * N + JA[i][None, :] * N + MT[:, sv[i]]
    for j in (0, 1):
        Ii, Cc = BL[j]
        sj = sv[Ii, Cc]
        nbr[2 * N + j * N:2 * N + (j + 1) * N] = Ii[None, :] * N + MT[:, inv[sj]]
    return nbr


def _cost(nbr, N):
    """Unreached vertices summed over the four class representatives, within distance D_TARGET."""
    V = 4 * N
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D_TARGET):
            nxt = nbr[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += V - int(np.count_nonzero(seen))
    return total


def _search_item(N, MT, inv, a, deadline, rng):
    """Simulated annealing for one (group, pattern). Returns the dart table sv with cost 0, or None."""
    JA, BL = _pattern(a)
    sv = _init_sv(N, JA, rng)
    cur = _cost(_build_nbr(MT, inv, sv, JA, BL, N), N)
    best, since = cur, 0
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = int(rng.integers(2))
        c = int(rng.integers(6))
        j = int(JA[i, c])
        used = {int(sv[i, cc]) for cc in range(6) if cc != c and int(JA[i, cc]) == j}
        x = int(rng.integers(N))
        while x in used:
            x = int(rng.integers(N))
        old = int(sv[i, c])
        sv[i, c] = x
        new = _cost(_build_nbr(MT, inv, sv, JA, BL, N), N)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best, since = cur, 0
        else:
            sv[i, c] = old
        since += 1
        if since > 3000:
            sv = _init_sv(N, JA, rng)
            cur = _cost(_build_nbr(MT, inv, sv, JA, BL, N), N)
            best, since = cur, 0
    return sv


def _edges(nbr, N):
    """Edges of the lift; every edge is listed once from its A-endpoint."""
    rows = nbr[:2 * N].tolist()
    edges = [(v, w) for v, row in enumerate(rows) for w in row]
    return 4 * N, edges


def _search_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    rng = np.random.default_rng(seed)
    groups = _group_list(NLO, NHI)
    items = [(g, a) for g in groups for a in (3, 2, 1)]
    for idx, ((N, m, k, lam), a) in enumerate(items):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(items) - idx)
        try:
            MT, inv = _group(m, k, lam)
            sv = _search_item(N, MT, inv, a, end, rng)
            if sv is None:
                continue
            JA, BL = _pattern(a)
            nbr = _build_nbr(MT, inv, sv, JA, BL, N)
            n, edges = _edges(nbr, N)
        except Exception:
            continue
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def _haar_fallback(d, D):
    """The parent's valid smaller Haar graph, returned only if lib.is_valid accepts it."""
    MT, _ = _group_meta(33, 10, 26)
    S = sorted({0, 179, 116, 180, 47, 306})
    N = MT.shape[0]
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def _trivial(d, D):
    """Always-valid small graph for any other case."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    if D >= 2 and d >= 1:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return 2, [(0, 1)]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _trivial(d, D)
    try:
        g = _search_target(d, D, seed, time_limit)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        g = _haar_fallback(d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return _trivial(d, D)
