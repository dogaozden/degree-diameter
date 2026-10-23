"""Voltage-lift search for the bipartite degree-diameter problem at (d, D) = (6, 5).

NEW FAMILY.  The parent searched Haar graphs, which are lifts of a 2-vertex base with d parallel darts.
This program lifts larger base multigraphs instead:
  * a base with k vertices on each side and 6 darts at every base vertex (6k darts in total);
  * each dart (a, b, g) with a group element g, lifted over a finite group G of order N:
    (a, x) ~ (b, x*g) for all x in G.
The lift has 2*k*N vertices and is 6-regular, bipartite, and left-G-invariant.  Left multiplication by G
is an automorphism that is transitive on each fibre, so the diameter equals the maximum eccentricity of the
2k representatives (a, e) and (b, e).  Each candidate is therefore scored with 2k numpy BFS runs of depth
D.  Simulated annealing moves are voltage changes and swaps of B-endpoints between darts, with restarts.

Portfolio: SL(2,5) with k = 3 (order 720), metacyclic groups with k = 2 (order near 172-176, n = 688-704),
and metacyclic groups with k = 3 (order 112-120).  Any cost-0 lift is checked with lib.is_valid before it is
returned.  If none is found, the parent's valid 660-vertex Haar graph is returned, so the score is never 0.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)."""
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
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1), identity first."""
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


# ------------------------------------------------------------------------------------ lift search

PATIENCE = 3000
TEMP = 0.5


def _neighbors(MT, inv, k, bend, g):
    """6-regular neighbour array of the lift.  A-vertex (a, x) is a*N + x, B-vertex (b, y) is (k+b)*N + y.
    Dart t joins A-base t//6 to B-base bend[t] with voltage g[t]; (a, x) ~ (b, x*g)."""
    N = MT.shape[0]
    E = 6 * k
    colsA = MT[:, g].reshape(N, k, 6).transpose(1, 0, 2)              # (k, N, 6): x*g
    offA = ((k + bend) * N).reshape(k, 6)
    NA = (colsA + offA[:, None, :]).reshape(k * N, 6)
    order = np.argsort(bend, kind="stable").reshape(k, 6)             # darts grouped by B-base
    gi = inv[g[order.ravel()]]
    valsB = MT[:, gi].reshape(N, k, 6).transpose(1, 0, 2)             # (k, N, 6): y*g^-1
    offB = (order // 6) * N
    NB = (valsB + offB[:, None, :]).reshape(k * N, 6)
    return np.vstack([NA, NB]).astype(np.int64)


def _cost(NB, k, N, D):
    """Total number of vertices not within distance D of the 2k representatives (0 = diameter <= D)."""
    n = 2 * k * N
    total = 0
    for s in list(range(k)) + [k + b for b in range(k)]:
        src = s * N
        vis = np.zeros(n, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = NB[front].ravel()
            cand = cand[~vis[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            vis[cand] = True
            front = cand
        total += n - int(vis.sum())
    return total


def _run_lift(MT, inv, k, deadline, rng, d, D):
    """Anneal voltages and B-endpoints of a random 6-regular base until the lift has diameter <= D.
    Returns a lib-checked (n, edges), or None."""
    N = MT.shape[0]
    E = 6 * k
    while time.monotonic() < deadline:
        bend = np.repeat(np.arange(k), 6)
        rng.shuffle(bend)
        g = rng.integers(0, N, size=E)
        NB = _neighbors(MT, inv, k, bend, g)
        cur = _cost(NB, k, N, D)
        runbest, since = cur, 0
        while cur > 0 and since < PATIENCE and time.monotonic() < deadline:
            if rng.random() < 0.6:
                bend2, g2 = bend, g.copy()
                t = int(rng.integers(E))
                g2[t] = rng.integers(N)
            else:
                bend2, g2 = bend.copy(), g
                t1, t2 = rng.choice(E, 2, replace=False)
                bend2[t1], bend2[t2] = bend[t2], bend[t1]
            NB2 = _neighbors(MT, inv, k, bend2, g2)
            c2 = _cost(NB2, k, N, D)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                bend, g, NB, cur = bend2, g2, NB2, c2
            since += 1
            if cur < runbest:
                runbest, since = cur, 0
        if cur == 0:
            n = NB.shape[0]
            src = np.repeat(np.arange(k * N), 6)
            dst = NB[:k * N].ravel()
            edges = sorted(set(zip(src.tolist(), dst.tolist())))
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _meta_candidates(orders, k):
    """(m, k, lam) with order m*k in orders, lam != 1, lam^k = 1 mod m (metacyclic Z_m x| Z_k)."""
    out = []
    for N in orders:
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


def _plan(rng):
    """(k, group builder, time weight) portfolio, in order of preference."""
    plan = [(3, (lambda: group_sl2(5)), 3.0)]
    c2 = _meta_candidates(range(172, 177), 2)
    if c2:
        m, k, lam = c2[int(rng.integers(len(c2)))]
        plan.append((2, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), 2.0))
    c3 = _meta_candidates(range(112, 121), 3)
    if c3:
        m, k, lam = c3[int(rng.integers(len(c3)))]
        plan.append((3, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), 2.0))
    return plan


# ------------------------------------------------------------------------------------- fallbacks

FALLBACK_TABLE = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """The valid 660-vertex Haar graph of the parent program, checked before use."""
    try:
        MT, _ = FALLBACK_TABLE[0]()
        n, edges = haar_edges(MT, FALLBACK_TABLE[1])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------------- entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.78 * time_limit
    rng = np.random.default_rng(seed)
    plan = _plan(rng)
    total_w = sum(w for _, _, w in plan)
    for k, builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            res = _run_lift(MT, inv, k, end, rng, d, D)
        except Exception:
            res = None
        if res is not None:
            return res
    return _fallback(d, D)
