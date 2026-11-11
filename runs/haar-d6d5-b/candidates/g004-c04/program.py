"""Bi-Cayley search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and four connection sets S_ij (i, j in {0, 1}) with
|S_00| = |S_11| = a and |S_01| = |S_10| = 6 - a (a in {2, 3, 4}), so every vertex has degree 6.
Vertices are A_i(g) and B_j(g) for g in G, with edges A_i(g) ~ B_j(g*s) for s in S_ij. Left multiplication
by any h in G is an automorphism, so the diameter is at most 5 iff the 4 base vertices A_0(e), A_1(e),
B_0(e), B_1(e) reach every vertex within 5 steps. The graph has 4N vertices, so N >= 172 beats the record 684.

NEW IN THIS VERSION.
  * Dense frontier coverage: the uncovered count is computed by a few float32 matrix products
    (adjacency matrix times a 4-column reachability matrix) instead of per-level Python/unique loops.
    This makes each move cheap enough to evaluate several proposals per step.
  * Best-of-K annealing: each step evaluates K random single-slot replacements and keeps the best one
    (Metropolis acceptance), with restarts when stuck.
  * Candidates are scanned in increasing order (N >= 172), each with a share of the remaining budget,
    so the largest valid graph found is returned.

Every returned graph is checked with lib.is_valid. If nothing is found, a valid Haar graph of order 660
(checked at run time) or a trivial valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 172          # 4 * 172 = 688 > 684 (record)
K_PROPOSALS = 4      # best-of-K proposals per annealing step
STALL_LIMIT = 500    # steps without progress before a restart
TEMP = 0.8
KEYS = [(0, 0), (0, 1), (1, 0), (1, 1)]


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- Haar fallback helpers

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


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------- bi-Cayley graph and cost

def _nbr(MT, inv, N, S):
    """Neighbour array (4N x DEG). Orbits: A_0 = 0..N-1, A_1 = N..2N-1, B_0 = 2N..3N-1, B_1 = 3N..4N-1.
    A_i(g) ~ B_j(g*s) for s in S[(i, j)]."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, DEG), dtype=np.int64)
    for i in (0, 1):
        c = 0
        for j in (0, 1):
            for s in S[(i, j)]:
                nbr[i * N:(i + 1) * N, c] = (2 + j) * N + MT[g, s]
                c += 1
    for j in (0, 1):
        c = 0
        for i in (0, 1):
            for s in S[(i, j)]:
                nbr[(2 + j) * N:(3 + j) * N, c] = i * N + MT[g, inv[s]]
                c += 1
    return nbr


def _dense(nbr, n):
    """Dense 0/1 adjacency matrix (float32) of a simple graph given as a neighbour array."""
    M = np.zeros((n, n), dtype=np.float32)
    M[np.repeat(np.arange(n), DEG), nbr.ravel()] = 1.0
    return M


def _uncovered(nbr, N):
    """Number of (source, vertex) pairs at distance > DIAM, over the four base vertices.
    0 means the graph has diameter <= DIAM. Computed with dense matrix products."""
    n = 4 * N
    M = _dense(nbr, n)
    X = np.zeros((n, 4), dtype=np.float32)
    for k, src in enumerate((0, N, 2 * N, 3 * N)):
        X[src, k] = 1.0
    for _ in range(DIAM):
        X = np.minimum(X + M @ X, 1.0)
    return int(4 * n - X.sum())


def _anneal(MT, inv, N, deadline, rng):
    """Best-of-K annealing over the four connection sets until uncovered = 0; return a checked (n, edges) or None."""
    n = 4 * N
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in KEYS}
        cur = _uncovered(_nbr(MT, inv, N, S), N)
        stall = 0
        while cur > 0 and stall < STALL_LIMIT and time.monotonic() < deadline:
            best_c, best_key, best_arr = None, None, None
            for _ in range(K_PROPOSALS):
                key = KEYS[int(rng.integers(4))]
                pos = int(rng.integers(sizes[key]))
                x = int(rng.integers(N))
                if x in S[key]:
                    continue
                arr = S[key].copy()
                arr[pos] = x
                old = S[key]
                S[key] = arr
                c = _uncovered(_nbr(MT, inv, N, S), N)
                S[key] = old
                if best_c is None or c < best_c:
                    best_c, best_key, best_arr = c, key, arr
            if best_key is None:
                stall += 1
                continue
            delta = best_c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                S[best_key] = best_arr
                cur = best_c
            stall = 0 if delta < 0 else stall + 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Non-abelian metacyclic groups with order in [MIN_N, 200), plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(MIN_N, 200):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam % m != 1:
                    out.append(("meta", m, k, lam))
                    break
    out = out[:12]
    out.append(("heis", 3, 7, 0))
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(c[1]), c[2])


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _anneal(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    if best is not None:
        return best
    return _fallback(d, D)
