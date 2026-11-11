"""Haar-graph race for the bipartite degree-diameter problem at (d, D) = (6, 5).

Each case is a Haar graph over a finite group G with a connection set S of d elements:
vertices (g, A) and (g, B), edges (g, A) ~ (s*g, B). The diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G, so the search minimises the number of uncovered
elements on both sides. Unlike the parent, the group pool is generated automatically:
every non-abelian metacyclic group Z_m x| Z_k with order in [343, 372], plus AGL(1,q) x Z_k,
Heisenberg and SL(2,5) products. Candidates are raced by successive halving. A group of
order 342 (AGL(1,19), giving 684 vertices, the record) is tried first. Every returned graph
is checked with lib.is_valid. Fallback: the parent's valid 660-vertex Haar graph, then a
tiny always-valid graph.
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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        xi = inv[X]
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score every single-slot replacement of S. Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, optionally starting from S0. Returns (best S, best cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
                return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


# --------------------------------------------------------------------------------------------- the graph

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


def safe_small(d, D):
    """Always-valid small graph for any other (d, D)."""
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        options.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        options.append((2, [(0, 1)]))
    options.append((1, []))
    for n, edges in options:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []


# ------------------------------------------------------------------------------------------- candidates

def meta_cands(lo, hi):
    """Metacyclic Z_m x|_lam Z_k candidates with order N = m*k in [lo, hi] (non-abelian, lam != 1)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1]
            pick = lams[:1] + lams[-1:] if len(lams) > 1 else lams[:1]
            for l in dict.fromkeys(pick):
                out.append({'name': f'meta {m}/{k}/{l}', 'N': N,
                            'build': (lambda m=m, k=k, l=l: group_meta(m, k, l)), 'S0': None})
    return out


STAGE_A = [
    # AGL(1,19), order 342: gives 684 vertices, matching the record.
    {'name': 'AGL(1,19)', 'N': 342, 'build': (lambda: group_agl(19)), 'S0': None},
]

NEAR = [
    ('meta 117/3/16', 351, lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21]),
    ('meta 71/5/5', 355, lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88]),
    ('SL(2,5)xZ3', 360, lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132]),
]

EXTRA = [
    ('Heis(7)', 343, lambda: group_heis(7)),
    ('Heis(3)xZ13', 351, lambda: group_times_cyclic(group_heis(3), 13)),
    ('AGL(1,9)xZ5', 360, lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5)xZ18', 360, lambda: group_times_cyclic(group_agl(5), 18)),
    ('AGL(1,7)xZ9', 378, lambda: group_times_cyclic(group_agl(7), 9)),
    ('AGL(1,3)xZ58', 348, lambda: group_times_cyclic(group_agl(3), 58)),
    ('AGL(1,3)xZ60', 360, lambda: group_times_cyclic(group_agl(3), 60)),
    ('AGL(1,4)xZ29', 348, lambda: group_times_cyclic(group_agl(4), 29)),
    ('AGL(1,4)xZ30', 360, lambda: group_times_cyclic(group_agl(4), 30)),
]

STAGE_B_CACHE = None


def stage_b():
    """All candidate groups of order >= 343 (the ones that could beat the record)."""
    global STAGE_B_CACHE
    if STAGE_B_CACHE is None:
        cands = [{'name': n, 'N': N, 'build': b, 'S0': s} for n, N, b, s in NEAR]
        cands += [{'name': n, 'N': N, 'build': b, 'S0': None} for n, N, b in EXTRA]
        cands += meta_cands(343, 372)
        STAGE_B_CACHE = cands
    return STAGE_B_CACHE


# ------------------------------------------------------------------------------------------ the race

def race(cands, deadline, rng, d, D):
    """Successive halving over candidate groups. Returns a checked (n, edges) or None."""
    if not cands:
        return None
    states = [{'c': c, 'MT': None, 'inv': None, 'best': 10 ** 9, 'dead': False} for c in cands]
    alive = states
    n = len(alive)
    rounds = int(math.ceil(math.log2(max(2, n)))) + 1
    slice_t = max(0.05, (deadline - time.monotonic()) / (n * rounds))
    while alive and time.monotonic() < deadline:
        for st in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            if st['MT'] is None:
                try:
                    st['MT'], st['inv'] = st['c']['build']()
                except Exception:
                    st['dead'] = True
                    continue
            end = min(deadline, now + slice_t)
            try:
                S, c = search(st['MT'], st['inv'], d, st['c'].get('S0'), end, rng)
            except Exception:
                st['dead'] = True
                continue
            if S is not None and c == 0:
                g = checked(st['MT'], S, d, D)
                if g is not None:
                    return g
            if c < st['best']:
                st['best'] = c
        alive = [s for s in alive if not s['dead']]
        alive.sort(key=lambda s: s['best'])
        alive = alive[:max(1, (len(alive) + 1) // 2)]
        slice_t *= 2
    return None


# ========================================================================================= build

TARGET = (6, 5)

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK_GROUP = lambda: group_meta(33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    best = None
    try:
        rng = np.random.default_rng(seed)
        total = deadline - time.monotonic()
        best = race(STAGE_A, time.monotonic() + 0.12 * total, rng, d, D)
        g = race(stage_b(), deadline, rng, d, D)
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    except Exception:
        pass
    if best is None:
        try:
            MT, _ = FALLBACK_GROUP()
            g = checked(MT, FALLBACK_S, d, D)
            if g is not None:
                best = g
        except Exception:
            pass
    if best is None:
        best = safe_small(d, D)
    return best
