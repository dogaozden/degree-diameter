"""Bi-Cayley lift search for the d=10, D=5 bipartite degree-diameter case.

Instead of a Haar graph (2 base vertices, all edges between them), this uses a
2+2 base multigraph lifted over a group G of order 1001..1100, giving 4|G| > 4000
vertices. Each base vertex has degree d. Left translation by G is an automorphism,
so the diameter is at most D iff, from each of the 4 base vertices at the identity,
the walks of length <= D reach every element of every fibre. The cost is the number
of uncovered (source, target fibre, element) triples. Simulated annealing over the
dart voltages drives the cost to 0. Any result is checked with lib.is_valid. A
precomputed valid 3582-vertex Haar graph is the fallback, so every case still
returns a valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given by integer coordinates (identity first) and a vectorised product."""
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
    """SL(2, p) for a prime p."""
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


def metacyclic_specs(lo, hi):
    """Specs ('meta', m, k, lam) for non-abelian Z_m x|_lam Z_k with lo <= m*k <= hi."""
    out = []
    for k in range(2, 11):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append(('meta', m, k, lam))
                    break
    return out


def make_group(spec):
    """Return (MT, inv) for a group spec."""
    if spec[0] == 'meta':
        _, m, k, lam = spec
        return group_meta(m, k, lam)
    if spec[0] == 'sl2x3':
        return group_times_cyclic(group_sl2(7), 3)
    if spec[0] == 'heisx3':
        return group_times_cyclic(group_heis(7), 3)
    raise ValueError(spec)


# -------------------------------------------------------------------- bi-Cayley lift search

def lift_cost(MT, MTT, inv, darts, D):
    """Uncovered (source, target fibre, element) triples; 0 iff the lift has diameter <= D."""
    N = MT.shape[0]
    out = [[] for _ in range(4)]
    for u, v, g in darts:
        out[u].append((v, MTT[g]))           # A-vertex x -> B-vertex x*g
        out[v].append((u, MTT[inv[g]]))      # B-vertex y -> A-vertex y*g^-1
    total = 0
    for s in range(4):
        front = np.zeros((4, N), dtype=bool)
        front[s, 0] = True
        ball = front.copy()
        for _ in range(D):
            nxt = np.zeros((4, N), dtype=bool)
            for u in range(4):
                idx = np.flatnonzero(front[u])
                if idx.size == 0:
                    continue
                for v, perm in out[u]:
                    nxt[v, perm[idx]] = True
            front = nxt
            ball |= front
        total += 4 * N - int(ball.sum())
    return total


def lift_edges(darts, N):
    """Edges of the lift: vertex u*N + x for base vertex u in 0..3."""
    edges = []
    for u, v, g in darts:
        col = MT_global[:, g]
        for x in range(N):
            edges.append((u * N + x, v * N + int(col[x])))
    return 4 * N, edges


MT_global = None


def anneal(MT, MTT, inv, d, D, deadline, rng, T=0.6, patience=2000):
    """Simulated annealing over dart voltages with random restarts. Returns (darts, cost)."""
    N = MT.shape[0]
    best, bestc = None, 1 << 60
    while time.monotonic() < deadline:
        a = int(rng.integers(1, d))
        pattern = [(0, 2, a), (0, 3, d - a), (1, 2, d - a), (1, 3, a)]
        darts = []
        for u, v, m in pattern:
            for g in rng.choice(N, m, replace=False):
                darts.append([u, v, int(g)])
        cur = lift_cost(MT, MTT, inv, darts, D)
        since = 0
        while time.monotonic() < deadline and since < patience:
            if cur < bestc:
                bestc = cur
                best = [list(x) for x in darts]
            if cur == 0:
                return best, 0
            t = int(rng.integers(len(darts)))
            u, v, old = darts[t]
            new = int(rng.integers(N))
            if new == old or any(du == u and dv == v and dg == new for du, dv, dg in darts):
                since += 1
                continue
            darts[t][2] = new
            c = lift_cost(MT, MTT, inv, darts, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                since = 0 if delta < 0 else since + 1
                if cur < bestc:
                    bestc = cur
                    best = [list(x) for x in darts]
                if cur == 0:
                    return best, 0
            else:
                darts[t][2] = old
                since += 1
    return best, bestc


# ------------------------------------------------------------------------- fallback graphs

FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    edges = [(int(a), int(N + MT[s, a])) for s in S for a in range(N)]
    return 2 * N, edges


def fallback_graph(d, D):
    """Valid 3582-vertex Haar graph (verified), or None."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != (10, 5):
        return trivial(d, D)

    global MT_global
    t0 = time.monotonic()
    fb = fallback_graph(d, D)
    budget = min(0.8 * time_limit, time_limit - 12.0)
    deadline = t0 + max(budget, 0.0)
    rng = np.random.default_rng(seed)

    specs = metacyclic_specs(1001, 1100) + [('sl2x3',), ('heisx3',)]
    for i in rng.permutation(len(specs)):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = min(deadline, now + 12.0)
        try:
            MT, inv = make_group(specs[i])
            N = MT.shape[0]
            if 4 * N <= 4000:
                continue
            MTT = np.ascontiguousarray(MT.T)
            MT_global = MT
            darts, c = anneal(MT, MTT, inv, d, D, slice_end, rng)
            if darts is not None and c == 0:
                n, edges = lift_edges(darts, N)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            continue

    if fb is not None:
        return fb
    return trivial(d, D)
