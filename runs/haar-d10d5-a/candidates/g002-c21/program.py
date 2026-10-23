"""Haar-graph search for the bipartite degree-diameter problem at diameter 5.

NEW IN THIS VERSION
1. Uncovered-word inversion (guided moves).  For a bad set S with uncovered element u, the pair-square word
   (x^-1 s_b)(s_c^-1 s_e) equals u exactly when x = (s_b s_c^-1 s_e) u^-1, and the side-1 word
   (x s_b^-1)(s_c s_e^-1) equals u exactly when x = u s_e s_c^-1 s_b.  So instead of sampling slot values
   at random, we solve for a slot value that covers a specific missing element.  Half the candidates in
   each annealing step come from this rule.
2. Successive halving over groups.  Several groups of order just above 2000 (metacyclic, Heisenberg mod 13,
   SL(2,13), SL(2,5) x Z_17) are annealed in rounds with doubling time slices.  After each round the worse
   half is dropped and its tables are freed.  Each survivor continues from its own best set.

Every returned graph is checked with lib.is_valid.  If nothing reaches cost 0, a valid smaller Haar graph
(the fallback) is returned.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
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


# ------------------------------------------------------------------------------ cover and cost

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
    """Cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
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


def uncovered(MT, inv, S):
    """The uncovered elements on each side for the current set S."""
    N = MT.shape[0]
    P0, P1 = _pairs(MT, inv, S)
    U0 = np.nonzero(~_cover(MT, N, np.unique(P0)))[0]
    U1 = np.nonzero(~_cover(MT, N, np.unique(P1)))[0]
    return U0, U1


# -------------------------------------------------------- NEW: uncovered-word inversion moves

def guided(MT, inv, S, rest, rng, k):
    """Candidate slot values that cover a randomly chosen uncovered element.

    Side 0: (x^-1 s_b)(s_c^-1 s_e) = u  gives  x = (s_b s_c^-1 s_e) u^-1.
    Side 1: (x s_b^-1)(s_c s_e^-1) = u  gives  x = u s_e s_c^-1 s_b.
    """
    if k <= 0:
        return np.empty(0, dtype=np.int64)
    U0, U1 = uncovered(MT, inv, S)
    sides = [(s, U) for s, U in ((0, U0), (1, U1)) if len(U) > 0]
    if not sides:
        return np.empty(0, dtype=np.int64)
    per = max(1, k // len(sides))
    out = []
    for side, U in sides:
        u = U[rng.integers(len(U), size=per)]
        b, c, e = rng.integers(len(rest), size=(3, per))
        sb, sc, se = rest[b], rest[c], rest[e]
        if side == 0:
            t = MT[MT[sb, inv[sc]], se]
            out.append(MT[t, inv[u]])
        else:
            out.append(MT[MT[u, se], MT[inv[sc], sb]])
    return np.concatenate(out).astype(np.int64)


# ----------------------------------------------------------------------------- annealing

def _random_set(N, d, rng):
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def _perturb(best, N, d, rng):
    S = best.copy()
    for i in rng.choice(d, 2, replace=False):
        S[i] = rng.integers(N)
    if len(set(S.tolist())) < d:
        return _random_set(N, d, rng)
    return S


def anneal(MT, inv, d, S0, deadline, rng, K=32, temp=0.4, patience=2500):
    """Annealing over d-subsets containing the identity, using random and guided candidates per step.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    S = _random_set(N, d, rng) if S0 is None else np.array(S0, dtype=np.int32)
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(d))
        rest = np.delete(S, i)
        X = np.concatenate([rng.integers(0, N, size=K // 2),
                            guided(MT, inv, S, rest, rng, K - K // 2)]).astype(np.int32)
        X = X[~np.isin(X, rest)]
        if X.size == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                continue
        since += 1
        if since > patience:
            since = 0
            S = _perturb(best, N, d, rng) if rng.random() < 0.5 else _random_set(N, d, rng)
            cur = cost(MT, inv, S)
            if cur < bestc:
                best, bestc = S.copy(), cur
    return best, bestc


# ------------------------------------------------------------------ successive halving over groups

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


def run_halving(cands, d, D, rng, t_end):
    """Anneal all candidate groups in rounds with doubling slices; keep the better half each round."""
    alive = cands
    slice_s = 2.0
    while alive and time.monotonic() < t_end:
        for g in alive:
            now = time.monotonic()
            if now >= t_end:
                break
            if g['MT'] is None:
                try:
                    g['MT'], g['inv'] = g['builder']()
                except Exception:
                    g['dead'] = True
                    continue
            end = min(t_end, now + slice_s)
            S, c = anneal(g['MT'], g['inv'], d, g['S'], end, rng)
            if g['S'] is None or c < g['c']:
                g['S'], g['c'] = S, c
            if g['c'] == 0:
                res = checked(g['MT'], g['S'], d, D)
                if res is not None:
                    return res
        alive = [g for g in alive if not g.get('dead')]
        alive.sort(key=lambda g: g['c'])
        keep = max(1, (len(alive) + 1) // 2)
        for g in alive[keep:]:
            g['MT'] = g['inv'] = None
        alive = alive[:keep]
        slice_s *= 2
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== target d10D5
TARGET = (10, 5)

# Metacyclic Z_m x|_lam Z_k with order m*k just above 2000 (lam^k = 1 mod m).
META_SPECS = [(101, 20), (41, 50), (29, 70), (31, 65), (61, 33), (79, 26)]

# Valid smaller Haar graph, checked at run time; used only when no group reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def _candidates():
    specs = [
        ("heis13", lambda: group_heis(13)),                                 # order 2197
        ("sl2_13", lambda: group_sl2(13)),                                  # order 2184
        ("sl2_5xZ17", lambda: group_times_cyclic(group_sl2(5), 17)),        # order 2040
    ]
    for m, k in META_SPECS:
        lam = next((l for l in range(2, m) if pow(l, k, m) == 1), None)
        if lam is not None:
            specs.append((f"Z{m}x|Z{k}", (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return [dict(name=n, builder=b, MT=None, inv=None, S=None, c=10 ** 9) for n, b in specs]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    t_end = t0 + max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    rng = np.random.default_rng(seed)
    try:
        g = run_halving(_candidates(), d, D, rng, t_end)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
