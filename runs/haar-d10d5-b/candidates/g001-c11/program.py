"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S of d elements, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices,
and has diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements.

NEW IN THIS VERSION: METACYCLIC SWEEP.  Instead of relying on one hand-picked group, the program enumerates
every metacyclic group Z_p x| Z_k with p prime, k | p-1, 2 <= k <= 10, whose order lies in a window around the
record threshold (|G| > 2000 beats the record 4000).  The automorphism lam is a primitive k-th root of unity mod p,
so it always has order exactly k and the group is non-abelian.  The candidates are searched round-robin with
slices that grow geometrically, so no single hard group can starve the others.  The first valid graph whose
order beats the record is returned at once.  Otherwise the largest valid graph found is returned.

Every returned graph is checked with lib.is_valid.  A checked, precomputed valid Haar graph of order 1791 is
always available as a floor.
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


# ----------------------------------------------------------------------------- new: metacyclic enumeration

def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _prime_factors(n):
    out, f = [], 2
    while f * f <= n:
        if n % f == 0:
            out.append(f)
            while n % f == 0:
                n //= f
        f += 1
    if n > 1:
        out.append(n)
    return out


def _primitive_root(p):
    fs = _prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return None


def metacyclic_candidates(lo, hi, kmax=10):
    """(order, m, k, lam) for Z_p x| Z_k with p prime, k | p-1, 2 <= k <= kmax, lo <= p*k <= hi.
    lam = g^((p-1)/k) for a primitive root g, so lam has order exactly k.
    Sorted so orders above 2000 come first (ascending), then orders below 2000 (descending)."""
    out = []
    for p in range(max(5, lo // kmax), hi // 2 + 1):
        if not _is_prime(p):
            continue
        g = None
        for k in range(2, kmax + 1):
            if (p - 1) % k or not (lo <= p * k <= hi):
                continue
            if g is None:
                g = _primitive_root(p)
            out.append((p * k, p, k, pow(g, (p - 1) // k, p)))
    out.sort(key=lambda t: (t[0] < 2001, t[0] if t[0] >= 2001 else -t[0]))
    return out


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of pair products)."""
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
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, with restarts.  Returns (best S, best cost); cost 0 = valid."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * (deadline - time.monotonic()))
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


# ------------------------------------------------------------------------------- new: round-robin sweep

def sweep(d, D, seed, deadline, cands, floor_n):
    """Round-robin search over candidate groups with geometrically growing slices.
    Returns the largest checked valid graph with more than floor_n vertices, or None.
    Returns as soon as a graph beats the record (n > 4000)."""
    rng = np.random.default_rng(seed)
    best = None
    slots = [dict(build=(lambda m=m, k=k, l=l: group_meta(m, k, l)), S0=S0, MT=None, inv=None, dead=False)
             for _, m, k, l, S0 in cands]
    slice_s = 0.8
    while time.monotonic() < deadline:
        progressed = False
        for c in slots:
            if c['dead']:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            if c['MT'] is None:
                try:
                    c['MT'], c['inv'] = c['build']()
                except Exception:
                    c['dead'] = True
                    continue
            end = min(deadline, now + slice_s)
            try:
                S, cst = search(c['MT'], c['inv'], d, c['S0'], end, rng)
            except Exception:
                c['dead'] = True
                continue
            c['S0'] = None
            progressed = True
            if S is not None and cst == 0:
                g = checked(c['MT'], S, d, D)
                if g is not None:
                    c['dead'] = True
                    if g[0] > floor_n and (best is None or g[0] > best[0]):
                        best = g
                    if g[0] > 4000:
                        return best
        if not progressed:
            break
        slice_s *= 1.5
    return best


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Valid smaller Haar graph (order 1791, 3582 vertices), checked at run time; the floor for this case.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def plan_candidates():
    """Candidate (order, m, k, lam, S0) list, most promising first, at most 10 entries."""
    near = (2005, 401, 5, 39, [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957])   # 6 short of valid
    second = (2016, 336, 6, 17, None)
    cands = [near, second] + [(o, m, k, l, None) for o, m, k, l in metacyclic_candidates(1792, 2100)]
    seen, out = set(), []
    for c in cands:
        key = (c[1], c[2])
        if key in seen:
            continue
        seen.add(key)
        out.append(c)
    return out[:10]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit

    best = None
    try:
        MT, _ = FALLBACK[0]()
        f = checked(MT, FALLBACK[1], d, D)
        if f is not None:
            best = f
    except Exception:
        pass

    floor_n = best[0] if best is not None else 0
    try:
        g = sweep(d, D, seed, deadline, plan_candidates(), floor_n)
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    except Exception:
        pass

    return best if best is not None else trivial(d, D)
