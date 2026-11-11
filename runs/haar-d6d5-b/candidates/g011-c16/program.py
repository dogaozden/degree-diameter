"""Haar-graph search for the bipartite degree-diameter problem, diameter 5, d = 6.

Construction: a Haar graph over a finite group G with connection set S (|S| = d) has 2|G| vertices,
is bipartite and d-regular, and has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
Changes in this version:
  * Candidate groups are metacyclic Z_m x| Z_k of every order in [343, 400], enumerated and
    shuffled within each order, instead of a fixed short list of families.
  * Heisenberg(7) and AGL-type products are kept as extra candidates after the metacyclic ones.
  * Each candidate gets a time slice; the search anneals S with incremental costs and restarts.
  * Every returned graph is checked with lib.is_valid. A precomputed valid order-330 Haar graph
    is the fallback, and a trivial always-valid graph covers the other (d, D) cases.
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
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and vectorised product mulfun."""
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


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b, a in the subgroup of order k of GF(q)^*. Default k = q-1 (AGL(1, q))."""
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
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only slot-i words are recomputed)."""
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
    """Simulated-annealing-style local search over d-subsets containing the identity. Returns (S, cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    S, cur, since = None, None, 0
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
        i = int(rng.integers(1, d))  # slot 0 stays the identity
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


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- candidate groups

def meta_candidates(lo, hi, rng):
    """Non-abelian metacyclic Z_m x| Z_k of order N = m*k in [lo, hi], shuffled within each order."""
    out = []
    for N in range(lo, hi + 1):
        bucket = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                bucket.append((m, k, lam))
        rng.shuffle(bucket)
        out.extend((N, m, k, lam) for m, k, lam in bucket[:12])
    return out


def candidate_plan(rng):
    """Ordered list of (name, builder) for the target case."""
    plan = []
    for N, m, k, lam in meta_candidates(343, 400, rng):
        plan.append((f"Z{m} x|{lam} Z{k}",
                     lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    plan.append(("Heis(7), order 343", lambda: group_heis(7)))
    plan.append(("AGL(1,9) x Z_5, order 360", lambda: group_times_cyclic(group_agl(9), 5)))
    plan.append(("AGL(1,5) x Z_18, order 360", lambda: group_times_cyclic(group_agl(5), 18)))
    return plan


# Valid smaller Haar graph, used only when no candidate reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])

TARGET = (6, 5)


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    plan = candidate_plan(rng)
    # Keep the number of tried groups bounded so each gets a meaningful slice.
    n_tries = min(len(plan), 12)
    for idx in range(n_tries):
        name, builder = plan[idx]
        now = time.monotonic()
        if now >= deadline_all:
            break
        slice_len = (deadline_all - now) / max(1, n_tries - idx)
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, now + slice_len, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            try:
                g = checked(MT, S, d, D)
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


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit)
