"""Two-orbit voltage lifts over metacyclic groups for the d=6, D=5 target (numpy only).

Construction: a 2+2 bipartite base multigraph (each base vertex of degree 6) whose darts carry
voltages in a group G of order N.  The lift has 4N vertices.  Edges are (a, g) ~ (b, s*g), so
right multiplication by G is an automorphism, and the diameter is at most 5 iff the four
vertices (a, e) and (b, e) all have eccentricity at most 5.  The search anneals the twelve
voltages on the cost (uncovered vertices within distance 5 of those four sources).  A found
lift is checked with lib.is_valid.  If nothing valid beats the record, the program falls back to
the valid Haar graph of order 660.  Every other (d, D) gets an always-valid small graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172          # 4 * 172 = 688 vertices, above the record 684
MAX_N = 186
SLICE = 1.3          # seconds of annealing per (group, base) candidate per pass


# ----------------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return MT


def _inverses(MT):
    return np.argmax(MT == 0, axis=1).astype(np.int64)


# ------------------------------------------------------------------- two-orbit lifts

def _darts(x):
    """Base multigraph: a0-b0 x darts, a0-b1 6-x, a1-b0 6-x, a1-b1 x (every vertex has degree 6)."""
    return [(0, 0, x), (0, 1, DEG - x), (1, 0, DEG - x), (1, 1, x)]


def _slots(x):
    out = []
    for a, b, c in _darts(x):
        out += [(a, b)] * c
    return out


def _adj(MT, inv, N, slots, volt):
    """6-regular adjacency of the lift.  A-vertex (a, g) = a*N+g, B-vertex (b, h) = 2N + b*N + h.
    Dart (a, b, s) gives edges (a, g) ~ (b, s*g)."""
    T = 4 * N
    ADJ = np.empty((T, DEG), dtype=np.int64)
    gs = np.arange(N, dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for (a, b), s in zip(slots, volt):
        ADJ[a * N + gs, ca[a]] = 2 * N + b * N + MT[s, gs]
        ca[a] += 1
        ADJ[2 * N + b * N + gs, cb[b]] = a * N + MT[inv[s], gs]
        cb[b] += 1
    return ADJ


def _ball(ADJ, src, depth):
    """Number of vertices within distance `depth` of src."""
    seen = np.zeros(ADJ.shape[0], dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(depth):
        nb = ADJ[frontier].ravel()
        nb = np.unique(nb[~seen[nb]])
        if nb.size == 0:
            break
        seen[nb] = True
        frontier = nb
    return int(seen.sum())


def _cost(ADJ, N):
    """Uncovered vertices, summed over the four representatives (a, e) and (b, e).  Zero = diameter <= 5."""
    T = 4 * N
    return sum(T - _ball(ADJ, src, DIAM) for src in (0, N, 2 * N, 3 * N))


def _lift_edges(ADJ, N):
    edges = []
    for a in range(2 * N):
        for b in ADJ[a]:
            edges.append((a, int(b)))
    return 4 * N, edges


def _anneal(MT, inv, N, x, rng, deadline):
    """Anneal the 12 voltages of the base multigraph.  Returns a zero-cost voltage list or None."""
    slots = _slots(x)
    nslot = len(slots)
    same = [[j for j in range(nslot) if j != i and slots[j] == slots[i]] for i in range(nslot)]

    def fresh():
        v = []
        for a, b, c in _darts(x):
            v += [int(t) for t in rng.choice(N, c, replace=False)]
        return v

    volt = fresh()
    cur = _cost(_adj(MT, inv, N, slots, volt), N)
    best = cur
    since = 0
    temp = 0.7
    patience = 1500
    while time.monotonic() < deadline:
        if cur == 0:
            return volt
        i = int(rng.integers(nslot))
        new = int(rng.integers(N))
        if any(volt[j] == new for j in same[i]):
            continue
        old = volt[i]
        volt[i] = new
        c = _cost(_adj(MT, inv, N, slots, volt), N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur < best:
                best = cur
                since = 0
            else:
                since += 1
        else:
            volt[i] = old
            since += 1
        if since > patience:
            volt = fresh()
            cur = _cost(_adj(MT, inv, N, slots, volt), N)
            best = cur
            since = 0
    return None


def _candidates(rng):
    """(N, m, k, lam, x) tuples for nonabelian Z_m x| Z_k of orders in [MIN_N, MAX_N], two base types each."""
    out = []
    for N in range(MIN_N, MAX_N + 1):
        cs = []
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    cs.append((m, k, lam))
        if not cs:
            continue
        order = rng.permutation(len(cs))
        for idx in order[:3]:
            m, k, lam = cs[int(idx)]
            for x in (3, 2):
                out.append((N, m, k, lam, x))
    return out[:40]


def _search(d, D, seed, time_limit):
    """Round-robin annealing over candidates.  Returns (n, edges) of the largest valid lift found, or None."""
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = np.random.default_rng(seed)
    cands = _candidates(rng)
    found = None
    minN = MIN_N
    while time.monotonic() < deadline:
        pool = [c for c in cands if c[0] >= minN]
        if not pool:
            break
        for N, m, k, lam, x in pool:
            if time.monotonic() >= deadline:
                break
            if N < minN:
                continue
            end = min(deadline, time.monotonic() + SLICE)
            try:
                MT = group_meta(m, k, lam)
                inv = _inverses(MT)
                volt = _anneal(MT, inv, N, x, rng, end)
                if volt is None:
                    continue
                ADJ = _adj(MT, inv, N, _slots(x), volt)
                if _cost(ADJ, N) != 0:
                    continue
                n, edges = _lift_edges(ADJ, N)
                if lib.is_valid(n, edges, d, D):
                    found = (n, edges)
                    minN = N + 1
            except Exception:
                continue
    return found


# ------------------------------------------------------------- fallback and trivial

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        found = _search(d, D, seed, time_limit)
        if found is not None:
            n, edges = found
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass
    try:
        MT = group_meta(33, 10, 26)
        g = checked_haar(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
