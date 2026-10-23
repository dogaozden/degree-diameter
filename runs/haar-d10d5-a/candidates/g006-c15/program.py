"""Combined bipartite degree-diameter search for the d=10, D=5 target.

Two searches share the time budget.

1. HAAR PHASE. A Haar graph on a group G with connection set S (|S| = d) is valid for diameter 5 iff
   (S^-1 S)^2 = G and (S S^-1)^2 = G. The search anneals S, scoring K random replacements per step with
   an incremental cost. A valid S for a group of order above 2000 gives more than 4000 vertices.

2. RANDOM PHASE. Random d-regular bipartite graphs of growing side size k, bisected to the largest k that
   passes lib.is_valid. Random graphs of this size may reach diameter 5 at orders the Haar search misses.

The fallback Haar graph (order 3582) is checked first. The largest graph that passes lib.is_valid is
returned. Other (d, D) cases get a small always-valid graph.
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


# ------------------------------------------------------------------------------ Haar search

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
    """Anneal over d-subsets of the group, from S0 (1-swap scan first) or from random sets.
    Returns (best S, best cost)."""
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


# ------------------------------------------------------------------- graphs and validity

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


def haar_phase(d, D, rng, end, plan):
    """Run the Haar plan until time `end`. Returns a checked valid graph or None."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= end:
            break
        slot_end = now + (end - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, slot_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    return None


# --------------------------------------------------------------- random bipartite regular

def random_bipartite(k, d, rng):
    """Simple d-regular bipartite graph on k+k vertices (A = 0..k-1, B = k..2k-1) as a union of d
    permutation matchings, with repairs to avoid repeated edges. Returns an edge list or None."""
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
    """Largest valid random bipartite graph found. `best` is a checked (n, edges) or None, lo its side size.
    Grows k geometrically while probes succeed, then bisects toward the first failing size."""
    hi = None
    k = max(lo + 1, 1800)
    dur = 0.0
    while time.monotonic() + 1.2 * dur + 0.2 < deadline:
        ok = None
        for _ in range(2):
            if time.monotonic() + 1.2 * dur + 0.2 >= deadline:
                break
            t = time.monotonic()
            e = random_bipartite(k, d, rng)
            if e is not None and lib.is_valid(2 * k, e, d, D):
                ok = (2 * k, e)
            dur = max(dur, time.monotonic() - t)
            if ok is not None:
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


# ------------------------------------------------------------------------------ entry point

TARGET = (10, 5)

# (name, group builder, start set S0 or None, share of the Haar phase).
PLAN = [
    ('meta 401/5/39, order 2005, 6 short',
     lambda: group_meta(401, 5, 39),
     [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957], 5),
    ('meta 336/6/17, order 2016', lambda: group_meta(336, 6, 17), None, 1),
]

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(3.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        g = haar_phase(d, D, rng, t0 + 0.5 * budget, PLAN)
        if g is not None and (best is None or g[0] > best[0]):
            best = g
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
