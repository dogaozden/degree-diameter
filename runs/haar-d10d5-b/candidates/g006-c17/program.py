"""Bi-orbit lift search for the bipartite degree-diameter problem at diameter 5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and a 2x2 base multigraph with parts {A0, A1} and {B0, B1}.
Pair (i, j) carries m_ij darts (voltage s in G), with row and column sums d.  The lift has vertices (g, X) for
X in {A0, A1, B0, B1} and g in G, with edges (g, A_i) ~ (s*g, B_j) for each dart (i, j, s).  The graph is
bipartite, d-regular, and has 4N vertices.  Right multiplication by G is an automorphism, so the diameter is at
most 5 iff a radius-5 BFS from each of the four identity vertices (e, A0), (e, A1), (e, B0), (e, B1) reaches
everything.  The cost is the number of unreached (source, vertex) pairs, computed by vectorised BFS.  Cost 0 means
valid, and every returned graph is re-checked with lib.is_valid.

SEARCH.  Simulated annealing over dart voltages (one voltage changed per step).  Within each base pair the
voltages stay distinct, so no multi-edges occur.  Restarts happen when the search stalls.  If no lift is valid,
the parent's valid Haar graph (3582 vertices) or a trivial graph is returned.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------- bi-orbit lift machinery

def _build_nbr(MT, inv, N, darts, d):
    """Neighbour matrix (4N, d) of the bi-orbit lift.  A_i vertex g is i*N+g, B_j vertex h is 2N+j*N+h.
    Dart (i, j, s): (g, A_i) ~ (s*g, B_j)."""
    V = 4 * N
    nbr = np.empty((V, d), dtype=np.int64)
    slot_out = [0, 0]
    slot_in = [0, 0]
    for i, j, s in darts:
        k = slot_out[i]
        slot_out[i] += 1
        nbr[i * N:(i + 1) * N, k] = 2 * N + j * N + MT[s].astype(np.int64)
        k2 = slot_in[j]
        slot_in[j] += 1
        nbr[2 * N + j * N: 2 * N + (j + 1) * N, k2] = i * N + MT[inv[s]].astype(np.int64)
    return nbr


def _uncovered(nbr, N):
    """Number of (source, vertex) pairs at distance > 5, sources = the four identity vertices."""
    V = nbr.shape[0]
    reach = np.zeros((4, V), dtype=bool)
    reach[np.arange(4), np.array([0, N, 2 * N, 3 * N])] = True
    for _ in range(5):
        reach = reach | reach[:, nbr].any(axis=2)
    return 4 * V - int(np.count_nonzero(reach))


def _cost(MT, inv, N, darts, d):
    return _uncovered(_build_nbr(MT, inv, N, darts, d), N)


def _graph(MT, inv, N, darts, d):
    nbr = _build_nbr(MT, inv, N, darts, d)
    A = nbr[:2 * N].tolist()
    edges = [(v, w) for v, row in enumerate(A) for w in row]
    return 4 * N, edges


def _search(MT, inv, N, a, d, rng, deadline):
    """Anneal dart voltages for base multiplicities [[a, d-a], [d-a, a]].  Returns darts with cost 0, or None."""
    pairs = [(0, 0, a), (0, 1, d - a), (1, 0, d - a), (1, 1, a)]

    def fresh():
        darts = []
        for i, j, c in pairs:
            for s in rng.choice(N, c, replace=False):
                darts.append([i, j, int(s)])
        return darts

    darts = fresh()
    cur = _cost(MT, inv, N, darts, d)
    best = cur
    since = 0
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        t = int(rng.integers(len(darts)))
        i, j, old = darts[t]
        s_new = int(rng.integers(N))
        if any(k != t and darts[k][0] == i and darts[k][1] == j and darts[k][2] == s_new
               for k in range(len(darts))):
            continue
        darts[t][2] = s_new
        c = _cost(MT, inv, N, darts, d)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            darts[t][2] = old
            since += 1
        if since > 3000:
            darts = fresh()
            cur = _cost(MT, inv, N, darts, d)
            best, since = cur, 0
    return darts if cur == 0 else None


# ---------------------------------------------------------------------------- fallbacks and helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5

TARGET = (10, 5)

LAM101 = next(x for x in range(2, 101) if pow(x, 10, 101) == 1 and pow(x, 5, 101) != 1 and pow(x, 2, 101) != 1)

# (name, group builder, [a], time weight).  a = multiplicity of the (0,0) and (1,1) base pairs.
PLAN = [
    ('meta 101/10, order 1010', lambda: group_meta(101, 10, LAM101), [5], 3),
    ('SL(2,7) x Z3, order 1008', lambda: group_times_cyclic(group_sl2(7), 3), [5], 2),
    ('Heis(7) x Z3, order 1029', lambda: group_times_cyclic(group_heis(7), 3), [5], 2),
    ('AGL(1,11) x Z10, order 1100', lambda: group_times_cyclic(group_agl(11), 10), [5], 2),
    ('meta 101/10 a=4', lambda: group_meta(101, 10, LAM101), [4], 1),
]

# Parent's valid Haar graph (3582 vertices), checked at run time; used only if no lift succeeds.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(p[3] for p in PLAN)
    results = []
    for name, builder, a_list, w in PLAN:
        now = time.monotonic()
        if now >= end_all:
            break
        end = now + (end_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            N = MT.shape[0]
            darts = _search(MT, inv, N, a_list[0], d, rng, end)
            if darts is not None:
                n, edges = _graph(MT, inv, N, darts, d)
                if lib.is_valid(n, edges, d, D):
                    results.append((n, edges))
        except Exception:
            continue
    if results:
        return max(results, key=lambda r: r[0])
    try:
        MT, _ = FALLBACK[0]()
        n, edges = haar_edges(MT, FALLBACK[1])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
