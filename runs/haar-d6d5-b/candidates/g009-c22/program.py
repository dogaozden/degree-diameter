"""Voltage-lift search for the bipartite degree-diameter problem (d=6, D=5), with a valid Haar fallback.

IDEA.  A lift of a small bipartite base multigraph with a A-vertices and a B-vertices (each of degree d) over a
finite group G (vertices (u, x), u a base vertex, x in G; dart (u, v, g) joins (u, x) to (v, x*g)) has
(2a)*|G| vertices.  Left multiplication by any h in G is an automorphism, so the diameter is at most D iff
every base vertex's representative (u, e) reaches all vertices within D steps.  That needs only 2a BFS runs
per evaluation, which makes annealing over the voltages cheap.  The base shapes (a = 2, 3) and matrices are
different from the Haar family (a = 1 with d parallel darts), so the search explores a different space.

SAFETY.  The valid Haar graph of order 660 is always built first and kept as the answer.  A lift replaces it
only if it passes lib.is_valid and is larger.  Other (d, D) cases get the small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
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
    """GF(q) x| C_k (default k = q-1, i.e. AGL(1, q)).  Product (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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


# ------------------------------------------------------------------------------------- lift evaluation

def _nbr_array(darts, MT, inv, N, nb, d):
    """Neighbour table (nb*N, d) of the lift.  Dart (u, v, g): (u, x) ~ (v, x*g), so (v, y) ~ (u, y*g^-1)."""
    xs = np.arange(N)
    nbr = np.empty((nb * N, d), dtype=np.int64)
    fill = [0] * nb
    for u, v, g in darts:
        nbr[u * N + xs, fill[u]] = v * N + MT[xs, g]
        fill[u] += 1
        nbr[v * N + xs, fill[v]] = u * N + MT[xs, inv[g]]
        fill[v] += 1
    return nbr


def _uncovered(nbr, nb, N, D):
    """Number of (base representative, vertex) pairs at distance > D.  Zero iff the lift has diameter <= D.

    Left multiplication is an automorphism, so the ball of (u, e) for each base vertex u decides the diameter.
    """
    n = nb * N
    total = 0
    for u in range(nb):
        seen = np.zeros(n, dtype=bool)
        s = u * N
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = np.unique(nbr[front].ravel())
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def _lift_search(MT, inv, a, M, end, rng, d, D, patience=3000):
    """Anneal the voltages of base matrix M (a x a, row and column sums d) over the group MT.
    Returns (n, edges) for a checked valid lift, or None."""
    N = MT.shape[0]
    nb = 2 * a
    pairs = [(i, j) for i in range(a) for j in range(a) if M[i][j] > 0]
    ks = [M[i][j] for i, j in pairs]

    def darts_of(volt):
        return [(i, a + j, g) for (i, j), gs in zip(pairs, volt) for g in gs]

    def cost_of(volt):
        return _uncovered(_nbr_array(darts_of(volt), MT, inv, N, nb, d), nb, N, D)

    def fresh():
        return [[int(x) for x in rng.choice(N, k, replace=False)] for k in ks]

    volt = fresh()
    cur = cost_of(volt)
    best_c, best_v = cur, [list(x) for x in volt]
    stall, T = 0, 1.0
    while cur > 0 and time.monotonic() < end:
        p = int(rng.integers(len(pairs)))
        t = int(rng.integers(len(volt[p])))
        g = int(rng.integers(N))
        if g in volt[p]:
            continue
        new = [list(x) for x in volt]
        new[p][t] = g
        c = cost_of(new)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            volt, cur = new, c
            if cur < best_c:
                best_c, best_v = cur, [list(x) for x in volt]
                stall = 0
        stall += 1
        if stall > patience:
            volt = fresh()
            cur = cost_of(volt)
            stall = 0
            if cur < best_c:
                best_c, best_v = cur, [list(x) for x in volt]
    if best_c != 0:
        return None
    n = nb * N
    edges = []
    for u, v, g in darts_of(best_v):
        col = MT[:, g]
        edges.extend((u * N + x, v * N + int(col[x])) for x in range(N))
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# --------------------------------------------------------------------------------- candidate families

MATS2 = [
    [[3, 3], [3, 3]],
    [[4, 2], [2, 4]],
    [[5, 1], [1, 5]],
]
MATS3 = [
    [[2, 2, 2], [2, 2, 2], [2, 2, 2]],
    [[3, 2, 1], [2, 2, 2], [1, 2, 3]],
    [[4, 1, 1], [1, 4, 1], [1, 1, 4]],
    [[3, 3, 0], [3, 0, 3], [0, 3, 3]],
]


def _combos(rng):
    """(total vertices, name, builder, base matrix, a) candidates whose order beats 684.
    a = 2 needs group order in [172, 200] and a = 3 needs [115, 135]."""
    specs = []
    for N in range(115, 201):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
            for lam in lams[:3]:
                specs.append((N, f"Z{m}x|Z{k}[{lam}]",
                              (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    specs += [
        (168, "SL23xZ7", lambda: group_times_cyclic(group_sl2(3), 7)),
        (192, "SL23xZ8", lambda: group_times_cyclic(group_sl2(3), 8)),
        (180, "AGL15xZ9", lambda: group_times_cyclic(group_agl(5), 9)),
        (168, "AGL17xZ4", lambda: group_times_cyclic(group_agl(7), 4)),
        (168, "AGL18xZ3", lambda: group_times_cyclic(group_agl(8), 3)),
        (189, "Heis3xZ7", lambda: group_times_cyclic(group_heis(3), 7)),
        (210, "AGL17xZ5", lambda: group_times_cyclic(group_agl(7), 5)),
    ]
    combos = []
    for N, name, builder in specs:
        if 172 <= N <= 200:
            for M in MATS2:
                combos.append((4 * N, name, builder, M, 2))
        if 115 <= N <= 135:
            for M in MATS3:
                combos.append((6 * N, name, builder, M, 3))
    if len(combos) > 120:
        idx = rng.choice(len(combos), 120, replace=False)
        combos = [combos[i] for i in idx]
    combos.sort(key=lambda c: c[0])
    return combos


# ------------------------------------------------------------------------------- safe fallbacks

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


# ------------------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    search_end = t0 + 0.72 * time_limit

    best = None
    try:
        MT, _ = group_meta(33, 10, 26)
        best = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
    except Exception:
        best = None
    best_n = best[0] if best is not None else 0

    rng = np.random.default_rng(seed)
    try:
        combos = _combos(rng)
    except Exception:
        combos = []

    found = None
    found_n = best_n
    while combos and time.monotonic() < search_end:
        progressed = False
        for ntot, name, builder, M, a in combos:
            now = time.monotonic()
            if now >= search_end:
                break
            if ntot <= found_n:
                continue
            progressed = True
            end = min(search_end, now + 1.0)
            try:
                MT, inv = builder()
                res = _lift_search(MT, inv, a, M, end, rng, d, D)
            except Exception:
                continue
            if res is not None and res[0] > found_n:
                found, found_n = res, res[0]
        if not progressed:
            break

    if found is not None and (best is None or found[0] > best[0]):
        return found
    if best is not None:
        return best
    return trivial(d, D)
