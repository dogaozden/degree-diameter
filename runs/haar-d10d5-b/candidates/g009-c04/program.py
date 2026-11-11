"""Two-orbit voltage lifts for the bipartite degree-diameter problem at (d, D) = (10, 5).

THEORY.  Let G be a finite group of order M with multiplication table MT (identity = 0).  Take four
fibres: A0, A1 (ids u*M + x, u in {0, 1}) and B0, B1 (ids v*M + x, v in {2, 3}).  Each dart (u, v, g)
joins u*M + x to v*M + MT[x, g] for all x in G.  The darts from A0 are k to B0 and d-k to B1, from A1
are d-k to B0 and k to B1, so every vertex has degree d and the graph has 4M vertices (bipartite).
Left multiplication by any h in G, x -> MT[h, x] on every fibre, is an automorphism.  Hence it is
enough to check distances from the four fibre identities: the graph has diameter <= D iff every vertex
is within distance D of each of the four sources.  The cost is the number of vertices left uncovered,
summed over the four sources, and the search anneals the voltages to drive it to 0.  Every returned
graph is checked with lib.is_valid.  If no lift is found in time, a precomputed valid Haar graph is
returned (or a trivial graph as a last resort).
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------- two-orbit lift search

def _lift_src_dst(MT, M, specs, volt):
    """Both directions of every lifted edge, as flat int64 arrays."""
    x = np.arange(M, dtype=np.int64)
    srcs, dsts = [], []
    for (u, v, _), gs in zip(specs, volt):
        for g in gs:
            a = u * M + x
            b = v * M + MT[x, g].astype(np.int64)
            srcs += [a, b]
            dsts += [b, a]
    return np.concatenate(srcs), np.concatenate(dsts)


def _nbr(MT, M, d, specs, volt):
    """Neighbour table of shape (4M, d)."""
    src, dst = _lift_src_dst(MT, M, specs, volt)
    order = np.argsort(src, kind="stable")
    return dst[order].reshape(4 * M, d)


def _uncov(nbr, M, D):
    """Uncovered vertices, summed over the four fibre identities, within distance D."""
    n = nbr.shape[0]
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[front].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def _anneal(MT, d, D, deadline, rng):
    """Anneal the voltages of one random two-orbit lift.  Returns a verified (n, edges) or None."""
    M = MT.shape[0]
    k = int(rng.integers(3, 8))
    specs = [(0, 2, k), (0, 3, d - k), (1, 2, d - k), (1, 3, k)]
    volt = [[int(g) for g in rng.choice(M, size=c, replace=False)] for _, _, c in specs]
    cur = _uncov(_nbr(MT, M, d, specs, volt), M, D)
    T = 1.5
    while cur > 0 and time.monotonic() < deadline:
        c = int(rng.integers(4))
        slot = int(rng.integers(len(volt[c])))
        g = int(rng.integers(M))
        if g in volt[c]:
            continue
        old = volt[c][slot]
        volt[c][slot] = g
        cand = _uncov(_nbr(MT, M, d, specs, volt), M, D)
        delta = cand - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = cand
        else:
            volt[c][slot] = old
    if cur != 0:
        return None
    x = np.arange(M, dtype=np.int64)
    edges = []
    for (u, v, _), gs in zip(specs, volt):
        for g in gs:
            edges.extend(zip((u * M + x).tolist(), (v * M + MT[x, g].astype(np.int64)).tolist()))
    n = 4 * M
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# Groups of order M with 4M > 4000 (so a success beats the record).  Each builder returns (MT, inv).
GROUP_BUILDERS = [
    lambda: group_times_cyclic(group_sl2(7), 3),        # order 1008
    lambda: group_times_cyclic(group_heis(7), 3),       # order 1029
    lambda: group_times_cyclic(group_agl(8), 18),       # order 1008
    lambda: group_meta(43, 24, 42),                     # order 1032
    lambda: group_meta(47, 22, 46),                     # order 1034
    lambda: group_meta(37, 28, 36),                     # order 1036
    lambda: group_meta(41, 25, 10),                     # order 1025
    lambda: group_meta(31, 33, 5),                      # order 1023
    lambda: group_times_cyclic(group_agl(13), 7),       # order 1092
    lambda: group_meta(101, 10, 100),                   # order 1010
]
SLICE = 6.0   # seconds per annealing run before restarting on the next group


def _search(d, D, deadline, rng):
    """Round-robin over the groups, restarting the annealing in fresh random slices."""
    cache = {}
    n_groups = len(GROUP_BUILDERS)
    i = 0
    while time.monotonic() < deadline - 0.5:
        idx = i % n_groups
        i += 1
        if idx not in cache:
            try:
                cache[idx] = GROUP_BUILDERS[idx]()[0]
            except Exception:
                cache[idx] = None
        MT = cache[idx]
        if MT is None:
            if all(v is None for v in cache.values()) and len(cache) == n_groups:
                break
            continue
        slice_end = min(deadline, time.monotonic() + SLICE)
        try:
            res = _anneal(MT, d, D, slice_end, rng)
        except Exception:
            res = None
        if res is not None:
            return res
    return None


# --------------------------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# Valid smaller Haar graph (order 3582), used only when no lift is found in time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
TARGET = (10, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    try:
        res = _search(d, D, deadline, rng)
    except Exception:
        res = None
    if res is not None:
        return res
    try:
        MT = FALLBACK[0]()[0]
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
