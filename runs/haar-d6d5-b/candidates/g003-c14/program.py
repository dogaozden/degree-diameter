"""Bi-Cayley search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and four connection sets S_ij (i, j in {0, 1}) with sizes
a, 6-a, 6-a, a, so every vertex has degree 6. Vertices are A_i(g) and B_j(g) for g in G, with edges
A_i(g) ~ B_j(g*s) for s in S_ij. Left multiplication by G is an automorphism, so the four base vertices
A_0(e), A_1(e), B_0(e), B_1(e) represent all orbits, and the diameter is at most 5 iff their radius-5 balls
cover the graph. The graph has 4N vertices, so N >= 172 beats the record 684.

NEW HELPER (targeted move).  Plain annealing replaces a random set element, which rarely helps. Here a move
picks an uncovered vertex u (distance > 5 from a random base vertex) and a vertex w within distance 4 of that
base vertex, of the opposite part. It then sets the connection element so that edge u ~ w exists. Such a move
reduces the uncovered count directly. A fraction of moves stay uniformly random for diversification.

COST(S) = number of (base vertex, target) pairs at distance > 5. Cost 0 means valid. Found graphs are checked
with lib.is_valid before being returned. If nothing is found in the budget, a valid order-660 Haar graph
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
MIN_N = 172   # 4 * 172 = 688 > 684 (record)
UNSEEN = 99   # distance sentinel (any value > DIAM)


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
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
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


# ------------------------------------------------------------------------- bi-Cayley graph and distances

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


def _dists(nbr, n, src):
    """BFS distances from src, truncated at DIAM. Unreached (or farther) vertices hold UNSEEN."""
    dist = np.full(n, UNSEEN, dtype=np.int16)
    dist[src] = 0
    fr = np.array([src], dtype=np.int64)
    for step in range(1, DIAM + 1):
        nx = np.unique(nbr[fr].ravel())
        nx = nx[dist[nx] == UNSEEN]
        if nx.size == 0:
            break
        dist[nx] = step
        fr = nx
    return dist


def _eval(nbr, N):
    """Return (cost, dists): cost = total uncovered (base vertex, target) pairs, dists = per-source BFS arrays."""
    n = 4 * N
    dists = [_dists(nbr, n, s) for s in (0, N, 2 * N, 3 * N)]
    cost = sum(int(np.count_nonzero(d == UNSEEN)) for d in dists)
    return cost, dists


# ------------------------------------------------------------------------------ targeted move (new)

def _random_move(N, sizes, keys, rng):
    key = keys[int(rng.integers(len(keys)))]
    return key, int(rng.integers(sizes[key])), int(rng.integers(N))


def _propose(MT, inv, N, sizes, keys, dists, rng):
    """Targeted move: pick an uncovered vertex u from a random base source and add an edge at u to a vertex
    within distance DIAM-1 of that source. Returns (key, pos, x) for the slot to overwrite."""
    if rng.random() < 0.25:
        return _random_move(N, sizes, keys, rng)
    d = dists[int(rng.integers(4))]
    unc = np.flatnonzero(d == UNSEEN)
    if unc.size == 0:
        return _random_move(N, sizes, keys, rng)
    u = int(unc[int(rng.integers(unc.size))])
    if u < 2 * N:
        # u = A_i(g): attach to a B_j(h) that is close to the source.
        i, g = u // N, u % N
        j = int(rng.integers(2))
        lo = 2 * N + j * N
        cand = np.flatnonzero(d[lo:lo + N] <= DIAM - 1)
        if cand.size == 0:
            return _random_move(N, sizes, keys, rng)
        h = int(cand[int(rng.integers(cand.size))])
    else:
        # u = B_j(h): attach to an A_i(g) that is close to the source.
        j, h = (u - 2 * N) // N, (u - 2 * N) % N
        i = int(rng.integers(2))
        lo = i * N
        cand = np.flatnonzero(d[lo:lo + N] <= DIAM - 1)
        if cand.size == 0:
            return _random_move(N, sizes, keys, rng)
        g = int(cand[int(rng.integers(cand.size))])
    x = int(MT[inv[g], h])   # A_i(g) ~ B_j(g * x) = B_j(h)
    key = (i, j)
    return key, int(rng.integers(sizes[key])), x


# ----------------------------------------------------------------------------------------- search

def _search(MT, inv, N, deadline, rng):
    """Anneal the four connection sets until cost 0; return a checked (n, edges) or None."""
    n = 4 * N
    while time.monotonic() < deadline:
        a = int(rng.choice([2, 3, 3, 4]))
        sizes = {(0, 0): a, (0, 1): DEG - a, (1, 0): DEG - a, (1, 1): a}
        keys = list(sizes)
        S = {k: rng.choice(N, size=sizes[k], replace=False).astype(np.int64) for k in keys}
        cur, dists = _eval(_nbr(MT, inv, N, S), N)
        stall = 0
        T = 0.5
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            key, pos, x = _propose(MT, inv, N, sizes, keys, dists, rng)
            if x in S[key]:
                stall += 1
                continue
            newS = dict(S)
            arr = S[key].copy()
            arr[pos] = x
            newS[key] = arr
            c, d2 = _eval(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur, dists = newS, c, d2
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nbr = _nbr(MT, inv, N, S)
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates(rng):
    """Non-abelian metacyclic groups of order in [MIN_N, 215], plus Heis(3) x Z_7 (order 189)."""
    out = []
    for NN in range(MIN_N, 216):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and pow(lam, 1, m) != 1:
                    out.append(("meta", m, k, lam))
                    break
    order = rng.permutation(len(out)) if out else []
    out = [out[int(i)] for i in order][:10]
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
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates(rng)
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    if best is not None:
        return best
    return _fallback(d, D)
