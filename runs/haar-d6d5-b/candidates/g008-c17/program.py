"""Diameter-5 bipartite search for d=6: 2+2 base-graph voltage lifts over non-abelian groups.

A parent Haar graph (one base vertex per side) reaches 2|G|. Here the base graph has two A-vertices and two
B-vertices, so the lift has 4|G| vertices. Voltages are searched by simulated annealing, and the cost is the
number of vertices missed by the radius-5 balls around the four base representatives. Left multiplication by
the group is an automorphism that is transitive on each fibre, so these four balls decide validity. A found
lift is re-checked with lib.is_valid. If nothing passes, the parent's valid 660-vertex Haar graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5
TEMP = 2.0
PATIENCE = 4000


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, identity index 0.  Needs lam^k = 1 mod m, gcd(lam, m) = 1."""
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


def group_agl(q, k=None):
    """GF(q) x| C_k, maps t -> a*t + b with a in the order-k subgroup of GF(q)^*; identity index 0."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------------------------- graph helpers

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2 and d >= 1:
        return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]   # K_{d,d}, diameter 2
    return 2, [(0, 1)]


# ------------------------------------------------------------- 2+2 base-graph voltage lifts

def _build_nb(MT, inv, N, V):
    """Neighbour array (4N, 6).  A_i,x = i*N + x; B_j,y = 2N + j*N + y.  Dart (i,j,g): A_i,x ~ B_j,x*g."""
    x = np.arange(N)
    nb = np.empty((4 * N, DEG), dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for i in range(2):
        for j in range(2):
            for g in V[i][j]:
                nb[i * N + x, ca[i]] = 2 * N + j * N + MT[x, g]
                ca[i] += 1
    for i in range(2):
        for j in range(2):
            for g in V[i][j]:
                nb[2 * N + j * N + x, cb[j]] = i * N + MT[x, inv[g]]
                cb[j] += 1
    return nb


def _missing(nb, src, n):
    """Number of vertices NOT within distance DIAM of src."""
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(DIAM):
        nxt = nb[frontier].ravel()
        nxt = np.unique(nxt[~seen[nxt]])
        if nxt.size == 0:
            break
        seen[nxt] = True
        frontier = nxt
    return n - int(seen.sum())


def _cost(MT, inv, N, V):
    nb = _build_nb(MT, inv, N, V)
    n = 4 * N
    return sum(_missing(nb, s, n) for s in (0, N, 2 * N, 3 * N))


def _lift_edges(MT, N, V):
    x = np.arange(N)
    edges = []
    for i in range(2):
        for j in range(2):
            for g in V[i][j]:
                ys = MT[x, g]
                edges += [(i * N + int(a), 2 * N + j * N + int(b)) for a, b in zip(x, ys)]
    return 4 * N, edges


def _anneal(MT, inv, N, M, deadline, rng):
    """Anneal voltages for base multiplicity matrix M.  Returns (best cost, best V)."""
    pairs = [(i, j) for i in range(2) for j in range(2) if M[i][j] > 0]

    def rand_state():
        V = [[[] for _ in range(2)] for _ in range(2)]
        for i, j in pairs:
            V[i][j] = [int(t) for t in rng.choice(N, M[i][j], replace=False)]
        return V

    def copy(V):
        return [[list(V[i][j]) for j in range(2)] for i in range(2)]

    V = rand_state()
    c = _cost(MT, inv, N, V)
    best_c, best_V = c, copy(V)
    since = 0
    while c > 0 and time.monotonic() < deadline:
        i, j = pairs[int(rng.integers(len(pairs)))]
        s = int(rng.integers(M[i][j]))
        g = int(rng.integers(N))
        if g in V[i][j]:
            continue
        old = V[i][j][s]
        V[i][j][s] = g
        c2 = _cost(MT, inv, N, V)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            c = c2
            if c < best_c:
                best_c, best_V = c, copy(V)
                since = 0
            else:
                since += 1
        else:
            V[i][j][s] = old
            since += 1
        if since > PATIENCE:
            V = rand_state()
            c = _cost(MT, inv, N, V)
            since = 0
    return best_c, best_V


M3 = [[3, 3], [3, 3]]
M2 = [[2, 4], [4, 2]]

# (group order N, group builder, base multiplicity matrix).  Ordered by N descending, so the first valid
# lift found is the largest among those tried.  A valid lift has 4N vertices; N >= 172 beats 684.
PLAN = [
    (200, lambda: group_agl(25, 8), M3),
    (190, lambda: group_meta(19, 10, 18), M3),
    (189, lambda: group_meta(7, 27, 2), M3),
    (184, lambda: group_meta(23, 8, 22), M3),
    (182, lambda: group_meta(13, 14, 12), M3),
    (180, lambda: group_meta(9, 20, 8), M3),
    (180, lambda: group_meta(9, 20, 8), M2),
    (176, lambda: group_meta(11, 16, 10), M3),
    (176, lambda: group_meta(11, 16, 10), M2),
    (172, lambda: group_meta(43, 4, 42), M3),
    (172, lambda: group_meta(43, 4, 42), M2),
    (171, lambda: group_meta(19, 9, 4), M3),
]


def _run_lift(seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    for k, (N, builder, M) in enumerate(PLAN):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(PLAN) - k)
        try:
            MT, inv = builder()
        except Exception:
            continue
        if MT.shape[0] != N:
            continue
        c, V = _anneal(MT, inv, N, M, end, rng)
        if c == 0:
            n, edges = _lift_edges(MT, N, V)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ----------------------------------------------------------------------------------- fallback

FALLBACK_GROUP = lambda: group_meta(33, 10, 26)          # valid Haar graph, 660 vertices
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = _run_lift(seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        MT, _ = FALLBACK_GROUP()
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
