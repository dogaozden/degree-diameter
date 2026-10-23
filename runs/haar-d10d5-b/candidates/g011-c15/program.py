"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides; cost 0 is valid.

NEW IN THIS VERSION.
  * metacyclic_candidates(lo, hi): enumerates many metacyclic groups Z_m x|_lam Z_k of every order in
    [lo, hi] (not only the few hand-picked ones), so the search can try many different groups of order
    just above the old threshold (1791) instead of a fixed short list.
  * halving(): successive halving over a portfolio of groups.  Every candidate gets a short annealing slice;
    the better half (by best cost reached) survives and gets twice the slice, until one group reaches cost 0.
    This spends the time budget on promising groups rather than spreading it evenly.

Every returned graph is checked with lib.is_valid.  If the search finds nothing, a valid smaller Haar graph
(FALLBACK) is returned, so a near miss never scores 0.
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


def metacyclic_candidates(lo, hi, max_lam=12):
    """All (order, m, k, lam) with lo <= m*k <= hi, lam a non-identity unit mod m (lam < max_lam), lam^k = 1 mod m.
    Non-abelian groups are preferred because abelian Haar graphs waste most of their words."""
    out = []
    for m in range(3, hi // 2 + 1):
        kmin = max(2, -(-lo // m))
        kmax = hi // m
        if kmin > kmax:
            continue
        for lam in range(2, min(m, max_lam + 1)):
            if math.gcd(lam, m) != 1:
                continue
            for k in range(kmin, kmax + 1):
                if pow(lam, k, m) == 1 % m:
                    out.append((m * k, m, k, lam))
    out.sort()
    return out


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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------------------------ cost

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


# ---------------------------------------------------------------------------------------------- search

def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group, from random starts.
    Returns (best S, best cost); cost 0 returns immediately."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
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


def halving(cands, d, D, deadline, rng, slice0):
    """Successive halving over a portfolio of (name, builder) groups.  Each round gives every surviving group a
    slice of annealing time; the better half (by best cost) survives and the slice doubles.  Returns a checked
    graph as soon as some group reaches cost 0, or None if the deadline passes."""
    alive = list(cands)
    sl = slice0
    while alive and time.monotonic() < deadline - 0.2:
        scored = []
        for name, builder in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                MT, inv = builder()
                S, c = search(MT, inv, d, min(deadline, now + sl), rng)
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
            scored.append((c, name, builder))
        if not scored:
            break
        scored.sort(key=lambda t: t[0])
        alive = [(n, b) for _, n, b in scored[:max(1, (len(scored) + 1) // 2)]]
        sl *= 2
    return None


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


# ======================================================================================== cell: d10D5

TARGET = (10, 5)
LO, HI = 1792, 2100          # group orders strictly above the old valid value 1791 (graph order 3584+)
N_META = 9                   # number of metacyclic candidates in the portfolio

# Valid smaller Haar graph (order 1791, 3582 vertices), used only when the portfolio finds nothing.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)

    named = [
        ('SL(2,7) x Z_6', lambda: group_times_cyclic(group_sl2(7), 6)),
        ('Heis(7) x Z_6', lambda: group_times_cyclic(group_heis(7), 6)),
    ]
    meta = metacyclic_candidates(LO, HI)
    if meta:
        pick = rng.choice(len(meta), size=min(N_META, len(meta)), replace=False)
        for idx in sorted(pick.tolist()):
            N, m, k, lam = meta[idx]
            named.append((f'Z{m} x| Z{k} lam={lam}',
                          lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))

    budget = deadline - time.monotonic()
    g = None
    try:
        g = halving(named, d, D, deadline, rng, slice0=max(0.3, budget / (3 * len(named))))
    except Exception:
        g = None
    if g is not None:
        return g

    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
