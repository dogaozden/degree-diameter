"""Bi-Cayley lifts with r orbits per side for the bipartite degree-diameter problem (diameter 5).

CONSTRUCTION.  Let G be a finite group of order N (metacyclic Z_m x| Z_k), and let r >= 1 be the number of
orbits per side.  Vertices are (i, g) on side A and (j, g) on side B, for orbit indices i, j < r and g in G,
stored as A: i*N + g and B: r*N + j*N + g.  For every block (i, j) choose a set S_ij of C[i][j] distinct group
elements, where C has all row and column sums d.  Each s in S_ij gives the edges (i, g) ~ (j, s*g) for all g.
The graph is bipartite, d-regular, and has 2*r*N vertices.  Right multiplication by G is an automorphism, so
each of the 2r orbit classes has one representative, and the diameter is at most D iff every representative
reaches all vertices within D steps.  The cost is the total number of vertices left unreached by those 2r
BFS balls.  Simulated annealing on the blocks drives the cost to 0.  Each candidate is checked with
lib.is_valid before return.  Groups of order N with r orbits give order 2rN, so r=2 needs N >= 172,
r=3 needs N >= 116, and r=4 needs N >= 86 to beat 684.

FALLBACK.  A valid Haar graph of order 660 is returned if no lift succeeds in time.  Other (d, D) cases get a
small always-valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
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


def meta_groups(lo, hi):
    """All (m, k, lam) with lo <= m*k <= hi, m >= 3, k >= 2, lam != 1 a unit with lam^k = 1 mod m (non-abelian)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
    return out


# ------------------------------------------------------------------------------- lift model

def random_C(r, d, rng):
    """r x r nonnegative integer matrix with all row and column sums d (sum of d random permutation matrices)."""
    C = np.zeros((r, r), dtype=np.int64)
    for _ in range(d):
        p = rng.permutation(r)
        C[np.arange(r), p] += 1
    return C


def _build_nbr(MT, inv, r, blocks, ar):
    """Neighbour array (n x d) of the lift.  A orbit i is i*N + g; B orbit j is r*N + j*N + h."""
    N = MT.shape[0]
    OFF = r * N
    n = 2 * OFF
    d = sum(len(blocks[(0, j)]) for j in range(r))
    nbr = np.empty((n, d), dtype=np.int64)
    for i in range(r):
        col = 0
        for j in range(r):
            for s in blocks[(i, j)]:
                nbr[i * N:(i + 1) * N, col] = OFF + j * N + MT[s, ar]
                col += 1
    for j in range(r):
        col = 0
        for i in range(r):
            for s in blocks[(i, j)]:
                nbr[OFF + j * N:OFF + (j + 1) * N, col] = i * N + MT[inv[s], ar]
                col += 1
    return nbr


def _cost(nbr, reps, n, D):
    """Total number of vertices not within distance D of the 2r class representatives (0 = diameter <= D)."""
    total = 0
    for rep in reps:
        seen = np.zeros(n, dtype=bool)
        seen[rep] = True
        front = np.array([rep], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        total += n - int(seen.sum())
    return total


def anneal(MT, inv, r, C, d, rng, deadline, D=5, T=0.7):
    """Anneal the connection blocks of an r-orbit lift.  Returns blocks with cost 0, or None at the deadline."""
    N = MT.shape[0]
    OFF = r * N
    n = 2 * OFF
    reps = [i * N for i in range(r)] + [OFF + j * N for j in range(r)]
    ar = np.arange(N)

    blocks = {}
    for i in range(r):
        for j in range(r):
            c = int(C[i][j])
            blocks[(i, j)] = [int(x) for x in rng.choice(N, c, replace=False)] if c else []
    keys = [k for k in blocks if blocks[k]]

    cur = _cost(_build_nbr(MT, inv, r, blocks, ar), reps, n, D)
    if cur == 0:
        return blocks
    while time.monotonic() < deadline:
        key = keys[int(rng.integers(len(keys)))]
        lst = blocks[key]
        t = int(rng.integers(len(lst)))
        new = int(rng.integers(N))
        if new in lst:
            continue
        old = lst[t]
        lst[t] = new
        c_new = _cost(_build_nbr(MT, inv, r, blocks, ar), reps, n, D)
        delta = c_new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c_new
            if cur == 0:
                return blocks
        else:
            lst[t] = old
    return None


def lift_graph(MT, r, blocks):
    """Explicit (n, edges) of the lift described by blocks."""
    N = MT.shape[0]
    OFF = r * N
    edges = []
    for (i, j), S in blocks.items():
        for s in S:
            row = MT[s]
            for g in range(N):
                edges.append((i * N + g, OFF + j * N + int(row[g])))
    return 2 * OFF, edges


# ---------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback_haar(d, D):
    """Valid Haar graph of order 660 (group Z_33 x| Z_10), checked; None on failure."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    S = [0, 179, 116, 180, 47, 306]
    edges = [(a, N + int(MT[s, a])) for s in S for a in range(N)]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# --------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + min(0.8 * time_limit, time_limit - 6.0)
    rng = np.random.default_rng(seed)

    pools = {2: meta_groups(172, 200), 3: meta_groups(116, 135), 4: meta_groups(86, 100)}
    choices = [2, 3, 3, 4]

    while time.monotonic() < deadline - 0.5:
        r = choices[int(rng.integers(len(choices)))]
        pool = pools[r]
        if not pool:
            continue
        m, k, lam = pool[int(rng.integers(len(pool)))]
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        C = random_C(r, d, rng)
        chunk_end = min(deadline, time.monotonic() + 6.0)
        try:
            blocks = anneal(MT, inv, r, C, d, rng, chunk_end, D)
        except Exception:
            blocks = None
        if blocks is not None:
            n, edges = lift_graph(MT, r, blocks)
            try:
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    try:
        g = _fallback_haar(d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
