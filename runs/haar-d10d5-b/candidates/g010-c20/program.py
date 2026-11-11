"""Four-orbit voltage-lift search for the bipartite degree-diameter problem, target d=10, D=5 (numpy only).

The parent searched single-orbit Haar graphs. This version tries a different construction. Take a group G of
order N in the range 1000 to 1400 and four orbits A1, A2, B1, B2. Each vertex is (g, X) with X one of the four
orbits, and each dart set S_ij (the group elements s with (g, A_i) ~ (s g, B_j)) has size c_ij, where
c = [[a, 10-a], [10-a, a]] so every vertex has degree 10. The graph is bipartite with 4N vertices. Right
multiplication by G is an automorphism, so the diameter is at most 5 iff each of the four orbit
representatives reaches every vertex within 5 steps. The cost is the total number of unreached vertices from
those four representatives, and cost 0 means valid. The cost is evaluated with vectorised numpy frontier
expansion, and the search is simulated annealing with restarts. Every result is checked with lib.is_valid.

If no valid four-orbit graph is found, the parent's valid single-orbit Haar graph (3582 vertices) is used as
the fallback. Other cases return a small verified graph.
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) for a prime power q: maps t -> a*t + b, a in GF(q)^*."""
    F = lib.GF(q)
    k = q - 1
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------ four-orbit lift (new construction)

def _nbr(MT, inv, S):
    """Neighbour array (4N, 10). Orbits: A1 = 0..N-1, A2 = N..2N-1, B1 = 2N..3N-1, B2 = 3N..4N-1.
    S[i][j] holds the dart set of (A_i, B_j): (g, A_i) ~ (s g, B_j)."""
    N = MT.shape[0]
    nbr = np.empty((4 * N, 10), dtype=np.int64)
    for i in range(2):
        nbr[i * N:(i + 1) * N] = np.concatenate(
            [MT[S[i][j]].T.astype(np.int64) + (2 + j) * N for j in range(2)], axis=1)
    for j in range(2):
        nbr[(2 + j) * N:(3 + j) * N] = np.concatenate(
            [MT[inv[S[i][j]]].T.astype(np.int64) + i * N for i in range(2)], axis=1)
    return nbr


def _cost(nbr, N, D=5):
    """Unreached vertices, summed over the four orbit representatives. 0 means valid."""
    V = 4 * N
    R = np.zeros((4, V), dtype=bool)
    R[np.arange(4), [0, N, 2 * N, 3 * N]] = True
    for _ in range(D):
        R = R | R[:, nbr].any(axis=2)
    return int(4 * V - R.sum())


def _anneal(MT, inv, rng, deadline):
    """Simulated annealing with restarts. Returns a valid dart structure S, or None."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        a = int(rng.integers(3, 8))
        sizes = [[a, 10 - a], [10 - a, a]]
        S = [[rng.choice(N, sizes[i][j], replace=False).astype(np.int64) for j in range(2)] for i in range(2)]
        cur = _cost(_nbr(MT, inv, S), N)
        rbest, stale = cur, 0
        while time.monotonic() < deadline and stale < 3000:
            if cur == 0:
                return S
            i, j = int(rng.integers(2)), int(rng.integers(2))
            pos = int(rng.integers(sizes[i][j]))
            x = int(rng.integers(N))
            if np.any(S[i][j] == x):
                continue
            old = S[i][j][pos]
            S[i][j][pos] = x
            c2 = _cost(_nbr(MT, inv, S), N)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / 2.0):
                cur = c2
                if c2 < rbest:
                    rbest, stale = c2, 0
                else:
                    stale += 1
            else:
                S[i][j][pos] = old
                stale += 1
        if cur == 0:
            return S
    return None


def _edges(MT, S):
    """Edge list of the four-orbit lift for S, with 4N vertices."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    parts = []
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                parts.append(np.stack([i * N + g, (2 + j) * N + MT[int(s)].astype(np.int64)], axis=1))
    E = np.concatenate(parts)
    return 4 * N, [(int(u), int(v)) for u, v in E]


# candidate groups of order 1000 to 1400 (four orbits give 4N vertices, which beats 4000 when N > 1000)
def _meta_101():
    p, k = 101, 10
    lam = next(x for x in range(2, p) if pow(x, k, p) == 1)
    return group_meta(p, k, lam)


PLAN_NEW = [
    ("Z101 x| Z10", _meta_101),
    ("SL(2,11)", lambda: group_sl2(11)),
    ("AGL(1,37)", lambda: group_agl(37)),
    ("Heisenberg(11)", lambda: group_heis(11)),
]


def _new_path(d, D, seed, deadline):
    rng = np.random.default_rng(seed)
    best = None
    for idx, (name, mk) in enumerate(PLAN_NEW):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(PLAN_NEW) - idx)
        try:
            MT, inv = mk()
            S = _anneal(MT, inv, rng, end)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, edges = _edges(MT, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            pass
    return best


# ------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def _fallback(d, D):
    """The parent's valid single-orbit Haar graph (order 1791, 3582 vertices), checked before use."""
    try:
        MT, _ = group_meta(199, 9, 180)
        S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return (n, edges)
    except Exception:
        pass
    return None


def trivial(d, D):
    """Small verified graph for any other (d, D)."""
    cand = None
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            cand = lib.projective_plane_incidence(d - 1)
        elif D >= 2 and d >= 1:
            cand = lib.haar_graph(d, range(d))
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            return cand
    except Exception:
        pass
    return (1, [])


# ------------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    try:
        if (d, D) != (10, 5):
            return trivial(d, D)
        deadline = t0 + 0.7 * time_limit
        best = _new_path(d, D, seed, deadline)
        if best is None:
            best = _fallback(d, D)
        if best is None:
            return trivial(d, D)
        return best
    except Exception:
        return trivial(d, D)
