"""Voltage-lift search for the bipartite degree-diameter problem (numpy only).

Different construction from the Haar search: the base graph has p = 2 A-vertices and p = 2 B-vertices.
Each A-base vertex has exactly k = d/p darts to each B-base vertex, and each dart carries a voltage in a
group G of order N, so the lift has 2pN = 4N vertices. Vertex (u, x) is adjacent to (v, x*g) for every dart
(u, v, g). Left multiplication by G is an automorphism, so the diameter is at most 5 iff a BFS of depth 5
from (u, e) reaches every vertex for each of the 2p base vertices u. Simulated annealing on the voltages
minimises the number of unreached vertices. Only a graph that passes lib.is_valid is returned. Otherwise
the program falls back to a verified Haar graph of order 3582.
"""
import itertools
import math
import time

import numpy as np

import lib


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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default k = q-1, that is AGL(1, q)). q a prime power."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
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


# ------------------------------------------------------------------------------- voltage-lift search

def build_neigh(MT, inv, G):
    """Neighbour array (2pN, d) of the lift. A-vertex (a, x) is id a*N + x; B-vertex (b, y) is id (p+b)*N + y.

    G[a, b, j] is the voltage of dart j from A-base a to B-base b. The dart uses A-slot b*k+j and B-slot a*k+j.
    """
    p, _, k = G.shape
    N = MT.shape[0]
    d = p * k
    nA = np.empty((p, N, d), dtype=np.int64)
    nB = np.empty((p, N, d), dtype=np.int64)
    for a in range(p):
        for b in range(p):
            for j in range(k):
                g = int(G[a, b, j])
                nA[a, :, b * k + j] = (p + b) * N + MT[:, g]
                nB[b, :, a * k + j] = a * N + MT[:, inv[g]]
    return np.concatenate([nA.reshape(p * N, d), nB.reshape(p * N, d)])


def _bfs_cost(neigh, n, starts, D):
    """Total number of vertices not within distance D of each start vertex."""
    total = 0
    for s in starts:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = neigh[fr].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            fr = nb
        total += n - int(np.count_nonzero(seen))
    return total


def lift_search(MT, inv, p, k, deadline, rng, D=5, patience=2500, T=0.8):
    """Simulated annealing over voltages with restarts. Returns (G, 0) on success, else (None, best cost)."""
    N = MT.shape[0]
    n = 2 * p * N
    starts = [v * N for v in range(2 * p)]

    def fresh():
        G = np.empty((p, p, k), dtype=np.int64)
        for a in range(p):
            for b in range(p):
                G[a, b] = rng.choice(N, k, replace=False)
        return G

    def cost_of(G):
        return _bfs_cost(build_neigh(MT, inv, G), n, starts, D)

    bestc = 10 ** 9
    while time.monotonic() < deadline:
        G = fresh()
        cur = cost_of(G)
        if cur == 0:
            return G, 0
        since = 0
        while time.monotonic() < deadline and since < patience:
            a = int(rng.integers(p))
            b = int(rng.integers(p))
            j = int(rng.integers(k))
            new = int(rng.integers(N))
            if new in G[a, b].tolist():
                continue
            old = int(G[a, b, j])
            G[a, b, j] = new
            c = cost_of(G)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                bestc = min(bestc, cur)
                if cur == 0:
                    return G.copy(), 0
                since = 0 if delta < 0 else since + 1
            else:
                G[a, b, j] = old
                since += 1
    return None, bestc


def graph_from_neigh(neigh, pN):
    """Edge list of the lift; every edge joins an A-row (id < pN) to a B-id."""
    d = neigh.shape[1]
    rows = np.repeat(np.arange(pN, dtype=np.int64), d)
    cols = neigh[:pN].ravel()
    return neigh.shape[0], list(zip(rows.tolist(), cols.tolist()))


# --------------------------------------------------------------------------------- Haar fallback

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


# ======================================================================================== cell: d10D5
TARGET = (10, 5)
P_BASE = 2                  # base vertices per side
LIFT_LO, LIFT_HI = 1001, 1100   # group orders N with 4N > 4000
NUM_METAS = 6


def meta_specs(lo, hi):
    """('meta', m, kk, lam) for Z_m x|_lam Z_kk with lo <= m*kk <= hi and lam != 1."""
    out = []
    for kk in range(2, 12):
        for m in range(max(2, -(-lo // kk)), hi // kk + 1):
            if m * kk < lo or m * kk > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1:
                    out.append(('meta', m, kk, lam))
                    break
    return out


def make_builder(spec):
    if spec[0] == 'heis':
        return group_times_cyclic(group_heis(7), 3)          # order 1029
    if spec[0] == 'agl':
        return group_times_cyclic(group_agl(11), 10)         # order 1100
    _, m, kk, lam = spec
    return group_meta(m, kk, lam)


# Verified valid smaller Haar graph (order 1791 group, 3582 vertices).
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    p = P_BASE
    k = d // p

    metas = meta_specs(LIFT_LO, LIFT_HI)
    idx = rng.permutation(len(metas))
    chosen = [('agl',), ('heis',)] + [metas[i] for i in idx[:NUM_METAS]]

    for i, spec in enumerate(chosen):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(chosen) - i)
        try:
            MT, inv = make_builder(spec)
            G, c = lift_search(MT, inv, p, k, end, rng, D=D)
        except Exception:
            continue
        if G is not None and c == 0:
            try:
                neigh = build_neigh(MT, inv, G)
                n, edges = graph_from_neigh(neigh, p * MT.shape[0])
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
