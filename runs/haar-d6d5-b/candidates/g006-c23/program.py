"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S of size d, the Haar graph has vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, with 2|G| vertices.  Its diameter is
at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides.

NEW IN THIS VERSION.
  * Uncovered-target moves.  If u is an element not covered by the side-0 words, then replacing slot i by
    x = s*u^-1 or x = s*u (s in S) puts u into the side-0 cover.  Likewise x = u*s or x = u^-1*s covers an
    uncovered side-1 element u.  The search draws candidates from these formulas, which makes it much more
    likely to hit a valid set than uniform random replacement.
  * Cost is computed directly from the uncovered sets, so the search does not need a separate cost routine.
  * Group list extended to metacyclic groups of order 342 (the record order) through 360.

Every returned graph is checked with lib.is_valid.  If no group reaches cost 0, a precomputed valid smaller
Haar graph is returned, so the score is not zero.
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a of order dividing k in GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------------------ covering

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def uncovered(MT, inv, S):
    """(uncovered side-0 elements, uncovered side-1 elements) of the set S, as index arrays."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]])
    P1 = np.unique(MT[S[:, None], Si[None, :]])
    return np.nonzero(~_cover(MT, N, P0))[0], np.nonzero(~_cover(MT, N, P1))[0]


def cost(MT, inv, S):
    """Number of uncovered elements over both sides (0 = valid diameter-5 Haar graph)."""
    U0, U1 = uncovered(MT, inv, S)
    return len(U0) + len(U1)


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


# ----------------------------------------------------------------------------------- new move helper

def targeted(MT, inv, S, U, rng, count):
    """Candidate replacements that put a randomly chosen uncovered element u into a cover.

    For s in S: s*u^-1 and s*u (side-0 words x^-1 s and s^-1 x equal u), u*s and u^-1*s (side-1 words
    x s^-1 and s x^-1 equal u).  At most `count` candidates are returned, sampled without repetition."""
    if len(U) == 0:
        return np.empty(0, dtype=np.int32)
    u = int(U[rng.integers(len(U))])
    ui = int(inv[u])
    s = S.astype(np.int64)
    cand = np.unique(np.concatenate([MT[s, ui], MT[s, u], MT[u, s], MT[ui, s]]))
    if len(cand) > count:
        cand = rng.choice(cand, count, replace=False)
    return cand.astype(np.int32)


# ------------------------------------------------------------------------------------------------ search

def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group, mixing uncovered-target candidates with random ones.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    S = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    cur, since = None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        rest = np.delete(S, i)
        cands = []
        if rng.random() < 0.6:
            U0, U1 = uncovered(MT, inv, S)
            U = np.concatenate([U0, U1]).astype(np.int64)
            cands.append(targeted(MT, inv, S, U, rng, K))
        cands.append(rng.integers(0, N, size=K).astype(np.int32))
        X = np.unique(np.concatenate(cands))
        X = X[~np.isin(X, rest)]
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
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

# (name, group builder, start set S0 or None, time weight).  Orders 342 (record) through 360.
PLAN = [
    ('Z19 x| Z18 (lam=2), order 342', lambda: group_meta(19, 18, 2), None, 3),
    ('Heis(7), order 343', lambda: group_heis(7), None, 2),
    ('Z43 x| Z8 (lam=-1), order 344', lambda: group_meta(43, 8, 42), None, 2),
    ('Heis(3) x Z13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 2),
    ('AGL(1,9) x Z5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 2),
    ('Z7 x| Z50 (lam=6), order 350', lambda: group_meta(7, 50, 6), None, 1),
]

# Valid smaller Haar graph (order 330, graph 660), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, PLAN, FALLBACK)
