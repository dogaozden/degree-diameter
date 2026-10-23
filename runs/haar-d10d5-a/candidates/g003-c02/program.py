"""Bi-Cayley lifts with two orbits per side (degree 10, diameter 5), with a verified Haar fallback.

CONSTRUCTION.  Take a finite group G of order N and four orbits A0, A1, B0, B1.  Vertex (x, v) has index
v*N + x (v = 0, 1 for A0, A1 and v = 2, 3 for B0, B1).  For each pair (i, j) in {0,1}^2 choose r = d/2 group
elements S[(i,j)].  Edges: (x, A_i) ~ (s*x, B_j) for s in S[(i,j)].  Every vertex then has degree 2r = d.
Right multiplication by h is an automorphism, so the diameter is at most D iff every vertex lies within
distance D of each of the four sources (e, A0), (e, A1), (e, B0), (e, B1).  The cost is the number of vertices
those four balls miss; cost 0 means the graph is valid.  Only a graph that passes lib.is_valid is returned.

The orbit count gives 4N vertices, so N >= 1001 is needed to beat the record of 4000.  A fallback that
is already valid (a smaller Haar graph) is used if no search reaches cost 0.  Other (d, D) cases return
the small always-valid graphs from before.
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


def _lam(m, k):
    """An element lam of exact multiplicative order k modulo the prime m (k must divide m - 1)."""
    for lam in range(2, m):
        if pow(lam, k, m) == 1 and all(pow(lam, t, m) != 1 for t in range(1, k)):
            return lam
    raise ValueError("no element of order %d mod %d" % (k, m))


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

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


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------ bi-Cayley construction

PAIRS = ((0, 0), (0, 1), (1, 0), (1, 1))   # (i, j): darts from A_i to B_j


def neighbours(MT, inv, S, r):
    """Neighbour table of the lift, shape (4N, 2r).  S has shape (4, r): group elements for each pair."""
    N = MT.shape[0]
    x = np.arange(N, dtype=np.int64)
    nb = np.empty((4 * N, 2 * r), dtype=np.int64)
    for p, (i, j) in enumerate(PAIRS):
        s = S[p]
        # (x, A_i) ~ (s x, B_j)
        nb[i * N:(i + 1) * N, j * r:(j + 1) * r] = (2 + j) * N + MT[s[None, :], x[:, None]]
        # (y, B_j) ~ (s^-1 y, A_i)
        nb[(2 + j) * N:(3 + j) * N, i * r:(i + 1) * r] = i * N + MT[inv[s][None, :], x[:, None]]
    return nb


def cost(nb, N, D):
    """Vertices missed by the radius-D balls around the four sources (e, class).  0 means diameter <= D."""
    V = 4 * N
    total = 0
    for src in range(4):
        vis = np.zeros(V, dtype=bool)
        s0 = src * N
        vis[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = cand[~vis[cand]]
            if cand.size == 0:
                break
            front = np.unique(cand)
            vis[front] = True
        total += V - int(vis.sum())
    return total


def search(MT, inv, r, deadline, rng, D):
    """Annealing over the 4 x r slot elements.  Returns (best S, best cost).  Restarts when stuck."""
    N = MT.shape[0]

    def rand_S():
        return np.stack([rng.choice(N, r, replace=False) for _ in PAIRS]).astype(np.int64)

    def score(S):
        return cost(neighbours(MT, inv, S, r), N, D)

    best_S, best_c = None, 1 << 60
    while time.monotonic() < deadline:
        if best_S is not None and rng.random() < 0.5:
            S = best_S.copy()
            for _ in range(3):
                p, t = int(rng.integers(4)), int(rng.integers(r))
                S[p, t] = rng.integers(N)
            if any(len(set(row.tolist())) < r for row in S):
                S = rand_S()
        else:
            S = rand_S()
        cur = score(S)
        stuck = 0
        T = 2.0
        while time.monotonic() < deadline and stuck < 4000:
            p = int(rng.integers(4))
            t = int(rng.integers(r))
            new = int(rng.integers(N))
            if new in S[p]:
                continue
            old = S[p, t]
            S[p, t] = new
            c = score(S)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                stuck = 0 if delta < 0 else stuck + 1
                if cur < best_c:
                    best_c, best_S = cur, S.copy()
                    if cur == 0:
                        return best_S, 0
            else:
                S[p, t] = old
                stuck += 1
    return best_S, best_c


def lift_graph(MT, inv, S, r):
    """Vertices: A0 = 0..N-1, A1 = N..2N-1, B0 = 2N..3N-1, B1 = 3N..4N-1."""
    N = MT.shape[0]
    nb = neighbours(MT, inv, S, r)
    edges = [(a, int(b)) for a in range(2 * N) for b in nb[a]]
    return 4 * N, edges


# ------------------------------------------------------------------------------ fallbacks and plan

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def haar_fallback(d, D):
    """Valid smaller Haar graph (order 3582) for d = 10, D = 5; None if it fails the check."""
    MT, _ = group_meta(199, 9, 180)
    S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
    N = MT.shape[0]
    edges = [(int(a), int(N + b)) for s in sorted(set(S)) for a, b in zip(range(N), MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


TARGET = (10, 5)

# (name, group builder, share of the search time).  Group orders N give 4N vertices.
PLAN = [
    ("Z101:Z10 (1010)", lambda: group_meta(101, 10, _lam(101, 10)), 2),
    ("SL(2,7)xZ3 (1008)", lambda: group_times_cyclic(group_sl2(7), 3), 2),
    ("Heis(7)xZ3 (1029)", lambda: group_times_cyclic(group_heis(7), 3), 2),
    ("AGL(1,13)xZ7 (1092)", lambda: group_times_cyclic(group_agl(13), 7), 1),
    ("Z137:Z8 (1096)", lambda: group_meta(137, 8, _lam(137, 8)), 1),
    ("SL(2,5)xZ9 (1080)", lambda: group_times_cyclic(group_sl2(5), 9), 1),
    ("Heis(5)xZ8 (1000)", lambda: group_times_cyclic(group_heis(5), 8), 1),
]


def run_target(d, D, seed, time_limit):
    """Search the plan in order; return a checked (n, edges) or None."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit - 1.0
    rng = np.random.default_rng(seed)
    r = d // 2
    total_w = sum(w for _, _, w in PLAN)
    for name, builder, w in PLAN:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, r, end, rng, D)
            if S is None or c != 0:
                continue
            n, edges = lift_graph(MT, inv, S, r)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            continue
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = run_target(d, D, seed, time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        res = haar_fallback(d, D)
        if res is not None:
            return res
    except Exception:
        pass
    return trivial(d, D)
