"""Combined bipartite degree-diameter search for the d=10, D=5 target.

Two searches share one time budget:

1. Haar-graph search (from the group-based parent). For a group G of order N > 2000 and a
   d-subset S, the Haar graph on 2N vertices has diameter <= 5 iff (S^-1 S)^2 = G and
   (S S^-1)^2 = G. Annealing over S drives the uncovered count to 0. Groups tried: metacyclic
   Z_m x| Z_k of order in [2000, 2100], AGL(1,47), SL(2,13), and Heisenberg mod 13.
2. Random bipartite d-regular graphs (from the other parent). Built as unions of d permutation
   matchings with repairs, then probed at growing side sizes with bisection. Used if the Haar
   stage fails to reach cost 0.

A valid Haar fallback of order 3582 is checked first. Only graphs passing lib.is_valid are
returned. Other (d, D) cases return a small always-valid graph.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a
    vectorised product mulfun(X, Y) on (..., c) arrays."""
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the pairwise products of P."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 products S_i^-1 S_j, side-1 products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements on both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only words involving slot i are recomputed)."""
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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group.
    Returns (best S, best cost); cost 0 means a valid Haar graph."""
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


# ------------------------------------------------------------------------- graph outputs

def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
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


# ------------------------------------------------------- random bipartite regular graphs

def random_bipartite(k, d, rng):
    """Simple d-regular bipartite graph on k+k vertices (A = 0..k-1, B = k..2k-1), a union of d
    permutation matchings with repairs. Returns an edge list, or None on failure."""
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
    """Find a large valid random bipartite graph. lo is the side size of `best` (already valid).
    Grows k geometrically while probes succeed, then bisects toward the first failing size."""
    hi = None
    k = max(lo + 1, 2000)
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
            best = ok
            lo = k
            if hi is None:
                k = int(k * 1.08) + 1
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


# ------------------------------------------------------------------------------ plan

TARGET = (10, 5)

# Metacyclic Z_m x|_lam Z_k of order m*k in [2000, 2100]. lam is any value with lam^k = 1 mod m.
META_SPECS = [(101, 20), (41, 50), (29, 70), (31, 65), (61, 33), (79, 26)]


def _meta_entries():
    out = []
    for m, k in META_SPECS:
        lam = next((l for l in range(2, m) if pow(l, k, m) == 1), None)
        if lam is not None:
            out.append((f"Z{m}x|Z{k}", (lambda m=m, k=k, l=lam: group_meta(m, k, l)), None, 1))
    return out


# Non-abelian groups of order above 2000 (2162, 2184, 2197), plus the metacyclic family.
PLAN = _meta_entries() + [
    ("AGL(1,47)", lambda: group_agl(47), None, 1),
    ("SL2(13)", lambda: group_sl2(13), None, 1),
    ("Heis13", lambda: group_heis(13), None, 1),
]

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def haar_stage(d, D, rng, end_all, plan):
    """Run the Haar searches in order, weighted, until end_all. Returns the first valid graph found, or None."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= end_all or total_w <= 0:
            break
        end = now + (end_all - now) * w / total_w
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
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        g = haar_stage(d, D, rng, t0 + 0.6 * budget, PLAN)
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    except Exception:
        pass

    if time.monotonic() + 3.0 < deadline:
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
