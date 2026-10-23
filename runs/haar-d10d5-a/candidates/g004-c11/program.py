"""Bold variant for d=10, D=5: non-Haar bipartite lifts over a finite group.

Base graph: vertices A0, A1, B0, B1, with C=5 darts between each (A_i, B_j) pair, so every
vertex has degree 10. For a group G of order m, dart s from A_i to B_j joins (g, A_i) to
(g*s, B_j). The graph has 4m vertices. Left multiplication is an automorphism, so the diameter
is at most 5 iff the radius-5 balls around (e, A0), (e, A1), (e, B0), (e, B1) cover all 4m
vertices. The search anneals the 20 dart elements against that uncovered-vertex count.

Safety: every returned graph is checked with lib.is_valid. If no search succeeds, a
valid smaller Haar graph is returned, and if that fails too, a trivial valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity)."""
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^*."""
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _meta_group(m, k):
    """Z_m x| Z_k with a nontrivial lam (lam^k = 1 mod m, lam != 1), or None if none exists."""
    for lam in range(2, m):
        if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
            return group_meta(m, k, lam)
    return None


# ------------------------------------------------------------------------- lift construction

DEG = 10          # target degree
C = 5             # darts per (A_i, B_j) pair; each vertex has degree 2*C = 10
TARGET = (10, 5)  # the (d, D) this plan is for
T0, T1 = 40.0, 0.5     # annealing temperatures (in units of uncovered vertices)
RESTART_SECS = 3.0     # length of one annealing run before a fresh random start

# Groups of order slightly above 1000 (so 4m > 4000). Tried in this order.
GROUPS = [
    ("SL(2,7) x Z3, order 1008", lambda: group_times_cyclic(group_sl2(7), 3)),
    ("Heis(7) x Z3, order 1029", lambda: group_times_cyclic(group_heis(7), 3)),
    ("Z37 x| Z28, order 1036", lambda: _meta_group(37, 28)),
    ("SL(2,5) x Z9, order 1080", lambda: group_times_cyclic(group_sl2(5), 9)),
    ("AGL-type GF(47) x| C23, order 1081", lambda: group_agl(47, 23)),
    ("Heis(5) x Z9, order 1125", lambda: group_times_cyclic(group_heis(5), 9)),
]


def _nbr(MT, inv, S, m):
    """Neighbour array (4m, DEG). A_i vertex g is i*m+g, B_j vertex h is 2m+j*m+h."""
    g = np.arange(m)
    nbr = np.empty((4 * m, DEG), dtype=np.int64)
    for i in range(2):
        col = 0
        for j in range(2):
            for s in S[i][j]:
                nbr[i * m:(i + 1) * m, col] = 2 * m + j * m + MT[g, s]
                col += 1
    for j in range(2):
        col = 0
        for i in range(2):
            for s in S[i][j]:
                nbr[2 * m + j * m:2 * m + (j + 1) * m, col] = i * m + MT[g, inv[s]]
                col += 1
    return nbr


def _cost(MT, inv, S, m):
    """Number of (source, vertex) pairs not within distance 5 of the four base sources. 0 = valid."""
    V = 4 * m
    nbr = _nbr(MT, inv, S, m)
    reach = np.zeros((4, V), dtype=bool)
    reach[0, 0] = True
    reach[1, m] = True
    reach[2, 2 * m] = True
    reach[3, 3 * m] = True
    for _ in range(5):
        new = reach | reach[:, nbr].any(axis=2)
        if np.array_equal(new, reach):
            break
        reach = new
    return 4 * V - int(reach.sum())


def _edges(MT, inv, S, m):
    """Edge list of the lift for S."""
    nbr = _nbr(MT, inv, S, m)
    edges = [(v, w) for v in range(2 * m) for w in nbr[v].tolist()]
    return 4 * m, edges


def _random_darts(rng, m):
    return [[rng.choice(m, C, replace=False).astype(np.int64) for _ in range(2)] for _ in range(2)]


def _copy(S):
    return [[a.copy() for a in row] for row in S]


def _anneal(MT, inv, m, deadline, rng):
    """Simulated annealing with random restarts. Returns (best S, best cost)."""
    best, bestc = None, 10 ** 18
    while time.monotonic() < deadline:
        S = _random_darts(rng, m)
        cur = _cost(MT, inv, S, m)
        if cur < bestc:
            best, bestc = _copy(S), cur
        if cur == 0:
            return best, 0
        t_start = time.monotonic()
        t_end = min(deadline, t_start + RESTART_SECS)
        while True:
            now = time.monotonic()
            if now >= t_end:
                break
            frac = (now - t_start) / max(1e-9, t_end - t_start)
            T = T0 * (T1 / T0) ** frac
            i, j = int(rng.integers(2)), int(rng.integers(2))
            p = int(rng.integers(C))
            x = int(rng.integers(m))
            if np.any(S[i][j] == x):
                continue
            old = S[i][j][p]
            S[i][j][p] = x
            c = _cost(MT, inv, S, m)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur < bestc:
                    best, bestc = _copy(S), cur
                    if cur == 0:
                        return best, 0
            else:
                S[i][j][p] = old
    return best, bestc


# ----------------------------------------------------------------------- fallback and trivial

def _haar(MT, S):
    """Haar graph of a table group: (g, A) ~ (s*g, B) for s in S."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in sorted({int(x) for x in S}) for a, b in zip(g, MT[s])]
    return 2 * N, edges


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)

    for idx, (name, builder) in enumerate(GROUPS):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(GROUPS) - idx)
        try:
            grp = builder()
            if grp is None:
                continue
            MT, inv = grp
            m = MT.shape[0]
            S, c = _anneal(MT, inv, m, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            try:
                n, edges = _edges(MT, inv, S, m)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    # Safe fallback: a checked, valid smaller Haar graph.
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = _haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
