"""Haar-graph search for the bipartite degree-diameter problem at diameter 5.

Ideas in this version (new relative to the parent):
  * Normalisation: left-translating S by h leaves the cost unchanged, so WLOG the identity 0 is always in S.
    Only slots 1..d-1 are ever moved, which shrinks the search space.
  * Greedy cover seeding: a start set is grown one element at a time, each step adding the candidate that
    covers the most of the required words (lowest partial cost). Restarts mix greedy and random seeds.
  * Structured proposals: besides uniform random replacements, the annealer proposes conjugates x s x^-1 and
    products s_a s_b of current set elements. These tend to hit cover gaps that uniform moves rarely reach.
  * Group enumeration: metacyclic groups Z_m x| Z_k of every order in a window just below and above the
    record threshold (2000), tried largest first, plus a few non-abelian groups of similar order.

Every returned graph is checked with lib.is_valid. If no group reaches cost 0 in its budget, a precomputed
valid smaller Haar graph is returned instead.
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


def group_agl(q):
    """AGL(1, q) for a prime power q: maps t -> a t + b."""
    F = lib.GF(q)
    H = list(range(1, q))
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


def candidate_groups(lo=1960, hi=2060, cap=7):
    """Metacyclic groups Z_m x| Z_k (non-abelian, lam != 1) with order in [lo, hi], largest order first."""
    found = {}
    for N in range(hi, lo - 1, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    found[N] = (m, k, lam)
                    break
            if N in found:
                break
        if len(found) >= cap:
            break
    return [(N, f"Z{m}x|Z{k}[{lam}]", (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
            for N, (m, k, lam) in found.items()]


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
    """Uncovered elements over both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


# ------------------------------------------------------------------------------------- seeds and moves

def random_seed(N, d, rng):
    """Random d-set containing the identity 0."""
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def greedy_seed(MT, inv, d, rng, ncand=120):
    """Grow a set from {0}: at each step add the sampled candidate that minimises the partial cost."""
    N = MT.shape[0]
    T = [0]
    for _ in range(d - 1):
        pool = np.unique(rng.integers(1, N, size=ncand))
        best_x, best_key = None, None
        for x in pool:
            x = int(x)
            if x in T:
                continue
            c = cost(MT, inv, np.array(T + [x], dtype=np.int32))
            key = c + rng.random() * 0.5
            if best_key is None or key < best_key:
                best_key, best_x = key, x
        if best_x is None:
            return random_seed(N, d, rng)
        T.append(best_x)
    return np.array(T, dtype=np.int32)


def _propose(MT, inv, S, i, K, rng):
    """Candidate replacements for slot i: uniform, conjugates x s x^-1, and products s_a s_b of kept elements."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    t = max(1, K // 3)
    u = rng.integers(0, N, size=t)
    xs = rng.integers(0, N, size=t)
    ss = rest[rng.integers(0, len(rest), size=t)]
    conj = MT[MT[xs, ss], inv[xs]]
    a = rest[rng.integers(0, len(rest), size=t)]
    b = rest[rng.integers(0, len(rest), size=t)]
    prod = MT[a, b]
    return np.concatenate([u, conj, prod]).astype(np.int32)


def anneal(MT, inv, d, S, deadline, rng, K=30, temp=0.4, patience=3000):
    """Metropolis search on slots 1..d-1 from S; returns (best S, best cost). Stops at cost 0 or stagnation."""
    S = S.copy()
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while cur > 0 and time.monotonic() < deadline and since <= patience:
        i = 1 + int(rng.integers(d - 1))
        rest = np.delete(S, i)
        X = _propose(MT, inv, S, i, K, rng)
        X = X[~np.isin(X, rest)]
        if len(X) == 0:
            since += 1
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc = S.copy(), cur
                since = 0
                continue
        since += 1
    return best, bestc


def search(MT, inv, d, deadline, rng):
    """Restarts: 70% greedy-cover seeds, 30% random seeds, each followed by an anneal."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        if rng.random() < 0.7:
            S = greedy_seed(MT, inv, d, rng)
        else:
            S = random_seed(N, d, rng)
        S, c = anneal(MT, inv, d, S, deadline, rng)
        if c < bestc:
            best, bestc = S.copy(), c
        if c == 0:
            return best, 0
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


def trivial(d, D):
    """Always-valid small graph for other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    g = lib.haar_graph(d, range(d))
    if lib.is_valid(g[0], g[1], d, D):
        return g
    return 2, [(0, 1)]


# Non-metacyclic groups of similar order, tried alongside the metacyclic ones.
EXTRA = [
    (2058, 'Heis7xZ6', lambda: group_times_cyclic(group_heis(7), 6)),
    (2028, 'AGL13xZ13', lambda: group_times_cyclic(group_agl(13), 13)),
    (2016, 'SL27xZ6', lambda: group_times_cyclic(group_sl2(7), 6)),
]

# Valid smaller Haar graph (order 2*1791), used only when no candidate reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    try:
        cands = candidate_groups() + EXTRA
    except Exception:
        cands = list(EXTRA)
    cands.sort(key=lambda t: -t[0])
    for idx, (N, name, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
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


def build(d, D, seed, time_limit):
    if (d, D) != (10, 5):
        return trivial(d, D)
    return run(d, D, seed, time_limit)
