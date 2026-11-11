"""Haar-graph search for the bipartite degree-diameter problem at diameter 5, with a group tournament.

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B) for
g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its
diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both
sides, and cost 0 means valid.

WHAT IS NEW HERE.  The parent tried three hand-picked groups.  This version adds:
  * metacyclic_candidates(lo, hi): every non-abelian metacyclic group Z_m x| Z_k (lam^k = 1 mod m, lam != 1)
    whose order lies in [lo, hi].  It enumerates the whole family in that order range.
  * tournament(pool, ...): successive halving over the candidate groups.  Each round gives every surviving
    group an equal time slice, continues each group's search from its best set so far, and keeps the better
    half.  Time concentrates on the groups whose best cost is lowest.
Every graph returned is checked with lib.is_valid.  If the tournament finds nothing, a precomputed valid
smaller Haar graph is returned, so a near miss never scores 0.
"""
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


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------------ candidate groups

def metacyclic_candidates(lo, hi):
    """All (m, k, lam) with lo <= m*k <= hi, k >= 2, m >= 3, lam a unit mod m with lam^k = 1 and lam != 1.
    Each triple gives a non-abelian group Z_m x|_lam Z_k."""
    out = []
    for k in range(2, hi + 1):
        m_lo = max(3, -(-lo // k))
        m_hi = hi // k
        for m in range(m_lo, m_hi + 1):
            if not lo <= m * k <= hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1:
                    continue
                if pow(lam, k, m) != 1 % m:
                    continue
                out.append((m, k, lam))
    return out


def _make_meta(m, k, lam):
    return lambda: group_meta(m, k, lam)


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        total += N - int(_cover(MT, N, np.unique(P)).sum())
    return total


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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score EVERY single-slot replacement of S.  Returns (best cost, best S)."""
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
    """Annealing over d-subsets of the group.  With a start set S0: scan its 1-swap neighbours, then anneal
    from it, restarting from a perturbed S0 or a random set when stuck.  Returns (best S, best cost)."""
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
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def tournament(pool, d, D, rng, deadline):
    """Successive halving over groups.  pool: list of (name, builder, S0 or None).
    Each round gives every alive group an equal slice of the remaining time, continuing from its best set so far.
    The worse half is dropped after each round.  Returns a checked graph or None."""
    alive = [{'name': n, 'builder': b, 'S0': s, 'tab': None, 'best': None, 'bestc': 10 ** 9, 'dead': False}
             for n, b, s in pool]
    while alive and time.monotonic() < deadline:
        rounds_left = int(math.ceil(math.log2(len(alive) + 1))) + 1
        remaining = deadline - time.monotonic()
        per = remaining / (rounds_left * len(alive))
        for c in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                if c['tab'] is None:
                    c['tab'] = c['builder']()
                MT, inv = c['tab']
                start = c['best'] if c['best'] is not None else c['S0']
                S, sc = search(MT, inv, d, start, min(deadline, now + per), rng)
            except Exception:
                c['dead'] = True
                continue
            if S is None:
                continue
            if sc == 0:
                try:
                    g = checked(MT, S, d, D)
                except Exception:
                    g = None
                if g is not None:
                    return g
                c['dead'] = True
                continue
            if sc < c['bestc']:
                c['bestc'] = sc
                c['best'] = np.array(S, dtype=np.int32).copy()
        alive = [c for c in alive if not c['dead']]
        if not alive:
            break
        alive.sort(key=lambda c: c['bestc'])
        alive = alive[:max(1, len(alive) // 2)]
    return None


# ======================================================================================== cell: d6D5
TARGET = (6, 5)
LO, HI = 342, 372          # group orders: 2|G| must reach the record 684 (|G| = 342) and beat it above that
NPOOL = 20                 # metacyclic candidates drawn at random from the order range

# Parent's near-miss seeds: (name, builder, start set S0 of element indices).
SEEDS = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21]),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88]),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132]),
]

# Valid smaller Haar graph (order 660), used only when the tournament finds nothing.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    try:
        pool = list(SEEDS)
        cands = metacyclic_candidates(LO, HI)
        if cands:
            picks = rng.permutation(len(cands))[:NPOOL]
            pool += [(f"meta {cands[i][0]}/{cands[i][1]}/{cands[i][2]}",
                      _make_meta(*cands[i]), None) for i in picks]
        g = tournament(pool, d, D, rng, deadline)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
