"""Bold variant: 2x2-base group lifts with direct BFS cost, plus the parent's Haar graph as a safe fallback.

For d=10, D=5 the new construction uses four base vertices (two A-fibres, two B-fibres) over a group G.
Each base pair (i, j) carries 5 darts s in G, giving the edges (i, g) ~ (j, s*g). Every vertex then has degree 10,
and the graph has 4|G| vertices. Right multiplication by any h is an automorphism, so the diameter is at most 5
iff each of the four representatives (fibre rep, identity) reaches the whole graph within 5 steps. The cost is the
total number of unreached vertices over those four BFS runs. Simulated annealing over the darts minimises that cost.
A cost-0 graph is checked with lib.is_valid before it is returned. Otherwise the parent's valid Haar graph is returned.
"""
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
    """Heisenberg group mod p, order p^3."""
    import itertools
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _find_lam(m, k):
    """An element of exact order k in Z_m^* (m prime, k | m-1)."""
    for x in range(2, m):
        if pow(x, k, m) == 1 and pow(x, k // 3 if k % 3 == 0 else 1, m) != 1:
            return x
    raise ValueError("no element of order k")


# ----------------------------------------------------------- 2x2-base lift: layout and cost

DARTS = 20          # 4 base pairs x 5 darts each
DEG = 10            # every base vertex has 10 darts
N_BASE = 4          # A0, A1 (ids 0,1), B0, B1 (ids 2,3)


def _slots():
    """Dart k joins A-fibre i = k // 10 with B-fibre j = (k // 5) % 2. Return per-dart in-slot index on its B-fibre."""
    inslot = [0] * DARTS
    count = {0: 0, 1: 0}
    for k in range(DARTS):
        j = (k // 5) % 2
        inslot[k] = count[j]
        count[j] += 1
    return inslot


INSLOT = _slots()


def build_nb(MT, inv, N, S):
    """Neighbour array (4N, DEG). A-fibre i is vertices i*N + g; B-fibre j is (2+j)*N + h."""
    nb = np.empty((N_BASE * N, DEG), dtype=np.int32)
    for k in range(DARTS):
        i = k // 10
        j = (k // 5) % 2
        s = int(S[k])
        nb[i * N:(i + 1) * N, k % 10] = (2 + j) * N + MT[s]
        nb[(2 + j) * N:(3 + j) * N, INSLOT[k]] = i * N + MT[int(inv[s])]
    return nb


def cost_of(nb, N):
    """Total number of vertices not reached within 5 steps from the four fibre representatives."""
    M = N_BASE * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        vis = np.zeros(M, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(5):
            nbrs = nb[fr].ravel()
            nbrs = nbrs[~vis[nbrs]]
            if nbrs.size == 0:
                break
            nbrs = np.unique(nbrs)
            vis[nbrs] = True
            fr = nbrs
        total += M - int(vis.sum())
    return total


def edges_of(MT, N, S):
    """Edge list of the lift for dart set S."""
    edges = []
    for k in range(DARTS):
        i = k // 10
        j = (k // 5) % 2
        s = int(S[k])
        row = MT[s]
        for g in range(N):
            edges.append((i * N + g, (2 + j) * N + int(row[g])))
    return N_BASE * N, edges


def anneal(MT, inv, N, rng, deadline, run_len):
    """Simulated annealing over the 20 darts. Each pair's 5 darts stay distinct. Returns (best S, best cost)."""
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        S = np.empty(DARTS, dtype=np.int64)
        for p in range(4):
            S[5 * p:5 * p + 5] = rng.choice(N, 5, replace=False)
        cur = cost_of(build_nb(MT, inv, N, S), N)
        if cur < bestc:
            best, bestc = S.copy(), cur
        if cur == 0:
            return best, 0
        t_start = time.monotonic()
        run_end = min(deadline, t_start + run_len)
        T0, T1 = 6.0, 0.15
        while True:
            now = time.monotonic()
            if now >= run_end:
                break
            frac = (now - t_start) / max(1e-9, run_end - t_start)
            T = T0 * (T1 / T0) ** frac
            k = int(rng.integers(DARTS))
            p = k // 5
            x = int(rng.integers(N))
            if x in S[5 * p:5 * p + 5]:
                continue
            old = S[k]
            S[k] = x
            c = cost_of(build_nb(MT, inv, N, S), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur < bestc:
                    best, bestc = S.copy(), cur
                    if cur == 0:
                        return best, 0
            else:
                S[k] = old
    return best, bestc


# ------------------------------------------------------------------ Haar fallback (safe, validated)

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------------- driver

TARGET = (10, 5)
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_lift(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.80 * time_limit
    rng = np.random.default_rng(seed)
    groups = [
        (0.6, lambda: group_meta(127, 9, _find_lam(127, 9))),   # order 1143, 4572 vertices
        (0.4, lambda: group_times_cyclic(group_heis(7), 3)),    # order 1029, 4116 vertices
    ]
    for share, builder in groups:
        now = time.monotonic()
        end = min(t0 + total, now + share * total)
        if now >= end:
            continue
        try:
            MT, inv = builder()
            N = MT.shape[0]
            S, c = anneal(MT, inv, N, rng, end, run_len=10.0)
        except Exception:
            continue
        if S is not None and c == 0:
            try:
                n, edges = edges_of(MT, N, S)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    res = run_lift(d, D, seed, time_limit)
    if res is not None:
        return res
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
