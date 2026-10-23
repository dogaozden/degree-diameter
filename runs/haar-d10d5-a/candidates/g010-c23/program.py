"""Two-orbit (and multi-orbit) group lifts for the bipartite degree-diameter problem, diameter 5, d = 10.

Parent approach: Haar graphs (one orbit per side) over groups of order about 2000.
New approach: lifts with r orbits per side. Vertices are (g, A_i) and (g, B_j) for g in a group G of order N,
and edges (g, A_i) ~ (s*g, B_j) for s in S_ij, where |S_ij| = C[i][j] and every row and column of C sums to d.
Such a graph has 2rN vertices. The map x -> x*k (right multiplication) is an automorphism, so the diameter is at
most 5 iff every one of the 2r sources (identity, class c) reaches all vertices within 5 steps. Cost = uncovered
(source, vertex) pairs, and simulated annealing drives it to 0. Orders are chosen so that 2rN > 4000.

Safety: a known valid Haar graph with 3582 vertices is checked with lib.is_valid first. Any lift returned must
pass lib.is_valid, otherwise the program falls back to that graph (or to a trivial construction).
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
SLICE = 8.0        # seconds of annealing per candidate group
FRACTION = 0.8     # share of time_limit used for searching
ANNEAL_LEN = 5000  # iterations per restart


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """GF(q) x| C_k (default k = q-1, that is AGL(1, q)).  q a prime power."""
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


# Base groups for product constructions: name -> (order, builder)
BASES = {
    'sl2_5': (120, lambda: group_sl2(5)),
    'sl2_7': (336, lambda: group_sl2(7)),
    'heis5': (125, lambda: group_heis(5)),
    'heis7': (343, lambda: group_heis(7)),
    'agl11': (110, lambda: group_agl(11)),
    'agl13': (156, lambda: group_agl(13)),
    'agl16': (240, lambda: group_agl(16)),
    'agl17': (272, lambda: group_agl(17)),
    'agl19': (342, lambda: group_agl(19)),
    'agl23': (506, lambda: group_agl(23)),
}


def _specs_of_order(N):
    """Group specs of order N: metacyclic Z_m x| Z_k, and base groups times Z_k."""
    specs = []
    for k in range(2, 13):
        if N % k == 0 and N // k >= 2:
            m = N // k
            lams = [lam for lam in range(2, m) if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1][:2]
            specs += [('meta', m, k, lam) for lam in lams]
    for name, (b, _) in BASES.items():
        if N % b == 0 and N // b >= 1:
            specs.append(('times', name, N // b))
    return specs


def _build_group(spec):
    if spec[0] == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    name, k = spec[1], spec[2]
    grp = BASES[name][1]()
    return group_times_cyclic(grp, k) if k > 1 else grp


def _candidates():
    """(r, circulant sizes, N, group spec) for lifts with 2rN > 4000."""
    plans = [
        (2, [5, 5], range(1001, 1101)),
        (2, [4, 6], range(1001, 1101)),
        (3, [4, 3, 3], range(667, 761)),
        (4, [3, 3, 2, 2], range(501, 581)),
    ]
    out = []
    for r, cvec, Ns in plans:
        for N in Ns:
            for spec in _specs_of_order(N):
                out.append((r, cvec, N, spec))
    return out


# ------------------------------------------------------------------------------------ lift structure

def _layout(r, C, d):
    """col[i][k] = target B-class of slot k in row i; pos[i][k] = slot index on the B side; bm = block mates."""
    col = [[] for _ in range(r)]
    for i in range(r):
        for j in range(r):
            col[i] += [j] * C[i][j]
    cntB = [0] * r
    pos = [[0] * d for _ in range(r)]
    for i in range(r):
        for k in range(d):
            j = col[i][k]
            pos[i][k] = cntB[j]
            cntB[j] += 1
    bm = [[[k2 for k2 in range(d) if col[i][k2] == col[i][k]] for k in range(d)] for i in range(r)]
    return col, pos, bm


def _random_S(rng, N, r, col, d):
    S = np.zeros((r, d), dtype=np.int64)
    for i in range(r):
        for j in set(col[i]):
            idx = [k for k in range(d) if col[i][k] == j]
            S[i, idx] = rng.choice(N, size=len(idx), replace=False)
    return S


def _set_slot(nbr, s, i, k, j, p, MT, inv, N, r):
    """Set A-vertex neighbour slot k of class i, and B-vertex neighbour slot p of class r+j, for element s."""
    ar = np.arange(N)
    nbr[i * N:(i + 1) * N, k] = (r + j) * N + MT[s, ar]
    nbr[(r + j) * N:(r + j + 1) * N, p] = i * N + MT[inv[s], ar]


def _build_nbr(S, MT, inv, N, r, col, pos, d):
    nbr = np.empty((2 * r * N, d), dtype=np.int64)
    for i in range(r):
        for k in range(d):
            _set_slot(nbr, int(S[i, k]), i, k, col[i][k], pos[i][k], MT, inv, N, r)
    return nbr


def _cost(nbr, r, N):
    """Uncovered (source, vertex) pairs at distance > 5 from the 2r sources (identity of each class)."""
    V = nbr.shape[0]
    R = np.zeros(V, dtype=np.uint64)
    for c in range(2 * r):
        R[c * N] |= np.uint64(1 << c)
    for _ in range(5):
        R = R | np.bitwise_or.reduce(R[nbr], axis=1)
    covered = 0
    for c in range(2 * r):
        covered += int(np.count_nonzero((R >> np.uint64(c)) & np.uint64(1)))
    return 2 * r * V - covered


def _anneal(MT, inv, N, r, C, d, rng, deadline):
    """Simulated annealing with restarts. Returns (S, 0, nbr) on success, else (None, None, None)."""
    col, pos, bm = _layout(r, C, d)
    while time.monotonic() < deadline:
        S = _random_S(rng, N, r, col, d)
        nbr = _build_nbr(S, MT, inv, N, r, col, pos, d)
        cur = _cost(nbr, r, N)
        if cur == 0:
            return S, 0, nbr
        T0, T1 = 2.0, 0.2
        for it in range(ANNEAL_LEN):
            if (it & 63) == 0 and time.monotonic() >= deadline:
                return None, None, None
            i = int(rng.integers(r))
            k = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S[i, bm[i][k]] == x):
                continue
            old = int(S[i, k])
            j = col[i][k]
            p = pos[i][k]
            S[i, k] = x
            _set_slot(nbr, x, i, k, j, p, MT, inv, N, r)
            new = _cost(nbr, r, N)
            delta = new - cur
            T = T0 * (T1 / T0) ** (it / ANNEAL_LEN)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                if cur == 0:
                    return S, 0, nbr
            else:
                S[i, k] = old
                _set_slot(nbr, old, i, k, j, p, MT, inv, N, r)
    return None, None, None


def _edges(nbr, r, N, d):
    us = np.repeat(np.arange(r * N, dtype=np.int64), d)
    vs = nbr[:r * N].ravel()
    return 2 * r * N, list(zip(us.tolist(), vs.tolist()))


# ------------------------------------------------------------------------------------- fallbacks

FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def _haar_fallback(d, D):
    """Valid Haar graph on 2*1791 = 3582 vertices, or None if it fails the check."""
    try:
        MT, _ = group_meta(199, 9, 180)
        N = MT.shape[0]
        S = sorted(set(FALLBACK_S))
        edges = [(int(a), int(N + MT[s, a])) for s in S for a in range(N)]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------------------------------- driver

def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + FRACTION * time_limit
    fallback = _haar_fallback(d, D)
    rng = np.random.default_rng(seed)
    cands = _candidates()
    order = rng.permutation(len(cands))

    i_c = 0
    while True:
        now = time.monotonic()
        if end - now < 1.5:
            break
        r, cvec, N, spec = cands[int(order[i_c % len(order)])]
        i_c += 1
        try:
            MT, inv = _build_group(spec)
            if MT.shape[0] != N:
                continue
            C = [[cvec[(j - i) % r] for j in range(r)] for i in range(r)]
            S, cost, nbr = _anneal(MT, inv, N, r, C, d, rng, min(end, now + SLICE))
        except Exception:
            continue
        if cost == 0 and nbr is not None:
            try:
                n, edges = _edges(nbr, r, N, d)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    if fallback is not None:
        return fallback
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run_target(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
