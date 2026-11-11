"""Bold attempt for d=10, D=5: voltage lifts of a 2+2 base multigraph over non-abelian groups.

THEORY.  Let G be a finite group and let the base graph have two A-vertices u in {0,1} and two B-vertices
v in {0,1}.  Each base dart (u, v, g) lifts to the edges (u, x) ~ (v, x*g) for all x in G.  The multiplicity
matrix is M = [[a, d-a], [d-a, a]], so every base vertex has degree d and the lift is d-regular and bipartite
on 4|G| vertices.  Left multiplication by h in G is an automorphism ((u,x) -> (u,hx)), so each base class is a
single orbit.  Diameter <= D holds iff the ball of radius D around each of the 4 sources (u, e) and (v', e) covers
all 4|G| vertices.  The cost is the total number of uncovered vertices over those 4 sources, and cost 0 means valid.

WHAT THIS FILE DOES.  Anneals the voltages (one dart changed per step, Metropolis acceptance, restarts) over
several non-abelian groups of order just above 1000, so the lift has more than 4000 vertices.  Every graph that
is returned has passed lib.is_valid.  If no lift succeeds, a checked Haar graph (order 1791, 3582 vertices) is
returned instead.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1); identity first."""
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q)); identity first."""
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


# ----------------------------------------------------------------------------- Haar fallback helpers

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


# ------------------------------------------------------------------------------ voltage-lift search

TEMP = 1.5
PATIENCE = 2500


def lift_cost(PFT, inv, k, darts, D):
    """Uncovered (source, vertex) pairs for the lift with the given darts (k = 2 base classes per side).

    PFT[g] is the map x -> x*g.  Sources are (u, e) on the A side and (v, e) on the B side; by left
    invariance these cover every vertex class.  Cost 0 means diameter <= D.
    """
    N = PFT.shape[0]
    S = 2 * k
    RA = np.zeros((S, k, N), dtype=bool)
    RB = np.zeros((S, k, N), dtype=bool)
    for u in range(k):
        RA[u, u, 0] = True
        RB[k + u, u, 0] = True
    ops = [(u, v, PFT[g], PFT[inv[g]]) for (u, v, g) in darts]
    for _ in range(D):
        nA = RA.copy()
        nB = RB.copy()
        for u, v, pf, pb in ops:
            nB[:, v, pf] |= RA[:, u, :]     # A (u, x) -> B (v, x*g)
            nA[:, u, pb] |= RB[:, v, :]     # B (v, y) -> A (u, y*g^-1)
        RA, RB = nA, nB
    covered = int(RA.sum()) + int(RB.sum())
    return S * 2 * k * N - covered


def anneal_lift(MT, inv, d, D, rng, deadline, k=2):
    """Search voltages for a valid lift.  Returns (darts, cost); cost 0 means a valid lift was found."""
    N = MT.shape[0]
    PFT = np.ascontiguousarray(MT.T)

    def fresh():
        a = int(rng.integers(1, d))            # a darts on (0,0) and (1,1), d-a on (0,1) and (1,0)
        M = [[a, d - a], [d - a, a]]
        darts = []
        for u in range(k):
            for v in range(k):
                for g in rng.choice(N, M[u][v], replace=False):   # distinct voltages avoid duplicate edges
                    darts.append((u, v, int(g)))
        return darts

    best, bestc = None, 10 ** 18
    done = False
    while not done and time.monotonic() < deadline:
        darts = fresh()
        cur = lift_cost(PFT, inv, k, darts, D)
        if cur < bestc:
            best, bestc = list(darts), cur
        since = 0
        while cur > 0 and since < PATIENCE and time.monotonic() < deadline:
            i = int(rng.integers(len(darts)))
            u, v, g_old = darts[i]
            g = int(rng.integers(N))
            if g == g_old or any(dd[0] == u and dd[1] == v and dd[2] == g for dd in darts):
                since += 1
                continue
            darts[i] = (u, v, g)
            c = lift_cost(PFT, inv, k, darts, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                if c < cur:
                    since = 0
                cur = c
                if cur < bestc:
                    best, bestc = list(darts), cur
                    if cur == 0:
                        done = True
                        break
            else:
                darts[i] = (u, v, g_old)
            since += 1
        if bestc == 0:
            break
    return best, bestc


def lift_graph(MT, k, darts):
    """Build the lift graph: A-vertex (u, x) is u*N + x, B-vertex (v, y) is k*N + v*N + y."""
    N = MT.shape[0]
    xs = np.arange(N)
    edges = set()
    for u, v, g in darts:
        A = u * N + xs
        B = k * N + v * N + MT[xs, g].astype(np.int64)
        edges.update(zip(A.tolist(), B.tolist()))
    return 2 * k * N, [(int(a), int(b)) for a, b in edges]


# ----------------------------------------------------------------------------------------- the program

TARGET = (10, 5)


def run_lift(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    plan = [
        (lambda: group_times_cyclic(group_sl2(7), 3), 3),        # order 1008 -> 4032 vertices
        (lambda: group_times_cyclic(group_heis(7), 3), 3),       # order 1029 -> 4116 vertices
        (lambda: group_times_cyclic(group_agl(13), 7), 2),       # order 1092 -> 4368 vertices
        (lambda: group_times_cyclic(group_agl(11), 10), 2),      # order 1100 -> 4400 vertices
    ]
    total_w = sum(w for _, w in plan)
    best = None
    for builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            darts, c = anneal_lift(MT, inv, d, D, rng, end, k=2)
            if darts is not None and c == 0:
                n, edges = lift_graph(MT, 2, darts)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
        except Exception:
            continue
    if best is not None:
        return best
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run_lift(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
