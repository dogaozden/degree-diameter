"""Combined bipartite degree-diameter search for the d=10, D=5 target.

Two searches share the budget. Both return only graphs that pass lib.is_valid.

1. Haar graphs over non-abelian groups of order 1792..2100 (metacyclic Z_m x| Z_k, SL(2,7) x Z_6,
   Heis(7) x Z_6). A Haar graph over G with connection set S of size d has 2|G| vertices and diameter
   at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Simulated annealing drives this cost to 0. Any
   valid group above order 1791 beats the fallback 3582, so the search only accepts larger groups
   after a success.
2. Random d-regular bipartite graphs. The side size grows from just above the best valid size, with
   bisection on failure.

The known valid Haar graph (order 3582) is checked first and used as the baseline.
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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
    """SL(2, p) for a prime p, order p(p^2-1), identity first."""
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


# ------------------------------------------------------------------------- Haar cost search

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
    """Cost of S with slot i replaced by x, for every x in the int array X."""
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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated annealing over d-subsets of the group with restarts. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    S, cur, since = random_set(), None, 0
    while time.monotonic() < deadline:
        if S is None:
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


# ------------------------------------------------------------------------------ graph output

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


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------- random bipartite search

def random_bipartite(k, d, rng):
    """Simple d-regular bipartite graph on k+k vertices (A = 0..k-1, B = k..2k-1), as a union of d
    permutation matchings with repairs to avoid repeated edges. Returns an edge list, or None on failure."""
    used = set()
    for _ in range(d):
        perm = [int(x) for x in rng.permutation(k)]
        bad = [i for i in range(k) if i * k + perm[i] in used]
        steps = 0
        while bad:
            steps += 1
            if steps > 200000:
                return None
            i = bad.pop()
            if i * k + perm[i] not in used:
                continue
            j = int(rng.integers(k))
            if j == i:
                continue
            perm[i], perm[j] = perm[j], perm[i]
            if (i * k + perm[i] in used) or (j * k + perm[j] in used):
                perm[i], perm[j] = perm[j], perm[i]
                bad.append(i)
        for i in range(k):
            used.add(i * k + perm[i])
    return [(c // k, k + c % k) for c in used]


def random_search(d, D, deadline, rng, best, lo):
    """Find a large valid random bipartite graph. lo is the side size of `best` (or 0).
    Grows k from just above lo, then bisects toward the first failing size."""
    hi = None
    k = max(lo + 1, 1000)
    while time.monotonic() + 1.5 < deadline:
        ok = None
        for _ in range(2):
            if time.monotonic() + 1.5 >= deadline:
                break
            e = random_bipartite(k, d, rng)
            if e is None:
                continue
            n = 2 * k
            if lib.is_valid(n, e, d, D):
                ok = (n, e)
                break
        if ok is not None:
            if best is None or ok[0] > best[0]:
                best = ok
            lo = k
            if hi is None:
                k = int(k * 1.03) + 1
            else:
                if hi - lo <= 1:
                    break
                k = (lo + hi) // 2
        else:
            hi = k
            if hi - lo <= 1:
                break
            k = (lo + hi) // 2
    return best


# ---------------------------------------------------------------------------- target setup

TARGET = (10, 5)
LO, HI = 1792, 2100  # valid group of order > 1791 already beats the fallback (2|G| > 3582)


def metacyclic_specs(lo, hi):
    """Specs (order, 'meta', m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi and lam != 1."""
    out = []
    for k in range(2, 11):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            lams = []
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    lams.append(lam)
                    if len(lams) >= 2:
                        break
            for lam in lams:
                out.append((m * k, 'meta', m, k, lam))
    return out


def make_builder(spec):
    kind = spec[1]
    if kind == 'meta':
        _, _, m, k, lam = spec
        return lambda: group_meta(m, k, lam)
    if kind == 'sl2':
        return lambda: group_times_cyclic(group_sl2(7), 6)
    if kind == 'heis':
        return lambda: group_times_cyclic(group_heis(7), 6)
    raise ValueError(kind)


FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def haar_phase(d, D, deadline, rng, best):
    """Try Haar groups in random order. A group is only tried if it can beat the current best."""
    specs = metacyclic_specs(LO, HI) + [(2016, 'sl2'), (2058, 'heis')]
    order = rng.permutation(len(specs))
    for pos, idx in enumerate(order):
        now = time.monotonic()
        if now >= deadline:
            break
        spec = specs[int(idx)]
        best_n = best[0] if best is not None else 0
        if 2 * spec[0] <= best_n:
            continue
        end = min(deadline, now + 5.0)
        try:
            MT, inv = make_builder(spec)()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and (best is None or g[0] > best[0]):
                best = g
    return best


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        best = haar_phase(d, D, t0 + 0.6 * budget, rng, best)
    except Exception:
        pass

    try:
        lo = best[0] // 2 if best is not None else 0
        found = random_search(d, D, deadline, rng, best, lo)
        if found is not None and (best is None or found[0] > best[0]):
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
