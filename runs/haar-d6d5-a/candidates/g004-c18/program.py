"""Multi-base voltage lifts over non-abelian groups for the d=6, D=5 bipartite case (numpy only).

NEW CONSTRUCTION.  Take a base bipartite multigraph with s A-vertices and s B-vertices, where each vertex has
degree 6 (row and column sums of the dart-count matrix M equal 6).  Each dart (A_i, B_j) carries a voltage g in G,
and the lift joins (A_i, x) to (B_j, x*g).  Left multiplication by any h in G is an automorphism, so every vertex
is equivalent to a base vertex with identity label.  The lift has diameter <= 5 iff, for each of the 2s base
vertices, the radius-5 ball from (base, identity) covers all 2s*|G| vertices.  Voltages are annealed to minimise the
number of uncovered (source, vertex) pairs.

SAFETY.  The valid 660-vertex Haar graph is computed first and kept as the answer.  Any lift result replaces it only
if it is larger and passes lib.is_valid.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

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
    e = np.array(list(__import__("itertools").product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    import itertools
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default AGL(1, q)), element (b, a) coded as the map t -> a*t + b."""
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


# ------------------------------------------------------------------------------------ Haar fallback

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


# ------------------------------------------------------------------------------ voltage-lift search

MATS = {
    2: [[[3, 3], [3, 3]], [[4, 2], [2, 4]], [[5, 1], [1, 5]]],
    3: [[[2, 2, 2], [2, 2, 2], [2, 2, 2]],
        [[3, 3, 0], [0, 3, 3], [3, 0, 3]],
        [[3, 2, 1], [1, 3, 2], [2, 1, 3]]],
}


def lift_search(MT, inv, s, M, deadline, rng, patience=5000, T=1.5):
    """Anneal dart voltages of the base graph with count matrix M.  Returns (cost, voltages, NB);
    NB is the neighbour table when cost is 0, else None."""
    N = MT.shape[0]
    VN = 2 * s * N
    darts = [(i, j) for i in range(s) for j in range(s) for _ in range(M[i][j])]
    Q = len(darts)
    sA = [0] * Q
    sB = [0] * Q
    cA = [0] * s
    cB = [0] * s
    for q, (i, j) in enumerate(darts):
        sA[q] = cA[i]
        cA[i] += 1
        sB[q] = cB[j]
        cB[j] += 1
    same = [[p for p in range(Q) if p != q and darts[p] == darts[q]] for q in range(Q)]
    xs = np.arange(N)
    srcs = np.arange(2 * s) * N
    invs = np.asarray(inv, dtype=np.int64)

    def set_dart(NB, q, g):
        i, j = darts[q]
        NB[i * N + xs, sA[q]] = (s + j) * N + MT[xs, g]
        NB[(s + j) * N + xs, sB[q]] = i * N + MT[xs, invs[g]]

    def cost(NB):
        reach = np.zeros((2 * s, VN), dtype=bool)
        reach[np.arange(2 * s), srcs] = True
        for _ in range(5):
            nxt = reach | reach[:, NB].any(axis=2)
            if np.array_equal(nxt, reach):
                break
            reach = nxt
        return int(2 * s * VN - reach.sum())

    best_c, best_v = 10 ** 9, None
    while time.monotonic() < deadline:
        volt = [0] * Q
        for q in range(Q):
            used = {volt[p] for p in same[q] if p < q}
            g = int(rng.integers(N))
            while g in used:
                g = int(rng.integers(N))
            volt[q] = g
        NB = np.zeros((VN, 6), dtype=np.int64)
        for q in range(Q):
            set_dart(NB, q, volt[q])
        cur = cost(NB)
        if cur == 0:
            return 0, volt, NB
        run_best, since = cur, 0
        while time.monotonic() < deadline and since < patience:
            q = int(rng.integers(Q))
            g = int(rng.integers(N))
            if g == volt[q] or any(volt[p] == g for p in same[q]):
                since += 1
                continue
            old = volt[q]
            set_dart(NB, q, g)
            c = cost(NB)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                volt[q] = g
                cur = c
                if cur == 0:
                    return 0, volt, NB
                if cur < run_best:
                    run_best, since = cur, 0
                else:
                    since += 1
            else:
                set_dart(NB, q, old)
                since += 1
        if run_best < best_c:
            best_c, best_v = run_best, list(volt)
    return best_c, best_v, None


def meta_list(lo, hi):
    """(name, m, k, lam, order) for metacyclic groups Z_m x| Z_k with order in [lo, hi] (one lam per (m, k))."""
    out = []
    for k in range(2, 60):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if not lo <= m * k <= hi:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((f"meta {m}/{k}/{lam}", m, k, lam, m * k))
                    break
    return out


def candidate_specs():
    """Entries (s, name, group builder, order): s = base side count, so the lift has 2*s*order vertices."""
    specs = []
    for name, m, k, lam, N in meta_list(166, 200):
        specs.append((2, name, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), N))
    for name, m, k, lam, N in meta_list(111, 133):
        specs.append((3, name, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), N))
    specs += [
        (2, 'AGL(1,5) x Z_9', lambda: group_times_cyclic(group_agl(5), 9), 180),
        (2, 'AGL(1,7) x Z_4', lambda: group_times_cyclic(group_agl(7), 4), 168),
        (3, 'SL(2,5)', lambda: group_sl2(5), 120),
        (3, 'Heis(5)', lambda: group_heis(5), 125),
        (3, 'AGL(1,8) x Z_2', lambda: group_times_cyclic(group_agl(8), 2), 112),
        (3, 'AGL(1,7) x Z_3', lambda: group_times_cyclic(group_agl(7), 3), 126),
        (3, 'AGL(1,5) x Z_6', lambda: group_times_cyclic(group_agl(5), 6), 120),
    ]
    return specs


def lift_edges(NB, s, N):
    """Edges of the lift from its neighbour table (A-ids 0..sN-1, B-ids sN..2sN-1)."""
    edges = []
    for a in range(s * N):
        for b in NB[a].tolist():
            edges.append((a, b))
    return 2 * s * N, edges


# ------------------------------------------------------------------------------------------ driver

# Valid 660-vertex Haar graph (order 330), used as the safe answer.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != (6, 5):
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + 0.72 * time_limit

    best, best_n = None, 0
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], 6, 5)
        if g is not None:
            best, best_n = g, g[0]
    except Exception:
        pass

    rng = np.random.default_rng(seed)
    specs = candidate_specs()
    order = rng.permutation(len(specs))
    k = 0
    while time.monotonic() < end - 1.0:
        if all(2 * sp[0] * sp[3] <= best_n for sp in specs):
            break
        s, name, builder, _ = specs[order[k % len(specs)]]
        k += 1
        if 2 * s * specs[order[(k - 1) % len(specs)]][3] <= best_n:
            continue
        try:
            MT, inv = builder()
            N = MT.shape[0]
            Ms = MATS[s]
            M = Ms[int(rng.integers(len(Ms)))]
            sl_end = min(end, time.monotonic() + 5.0)
            c, volt, NB = lift_search(MT, inv, s, M, sl_end, rng)
        except Exception:
            continue
        if NB is not None and c == 0:
            try:
                n, edges = lift_edges(NB, s, N)
                if n > best_n and lib.is_valid(n, edges, 6, 5):
                    best, best_n = (n, edges), n
            except Exception:
                pass

    return best if best is not None else trivial(d, D)
