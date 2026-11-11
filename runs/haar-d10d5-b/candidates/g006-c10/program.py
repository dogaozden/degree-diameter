"""Multi-orbit group lifts for the bipartite degree-diameter problem at diameter 5 (numpy only).

CONSTRUCTION.  Let G be a finite group of order N.  Take a orbits of A-type vertices and b orbits of B-type vertices,
each orbit a copy of G: (i, g) for A-orbit i and (j, h) for B-orbit j.  Pick a pattern M (a x b matrix of
nonnegative integers with all row and column sums d) and for each cell (i, j) a set S_ij of M_ij distinct group
elements.  Edges: (i, g) ~ (j, s*g) for s in S_ij.  The graph is bipartite, d-regular, has (a+b)*N vertices, and
right multiplication by any h in G is an automorphism that acts regularly on each orbit.  Hence the diameter is at
most D iff a BFS of depth D from one representative of every orbit reaches all vertices.  The Haar graph is the
case a = b = 1.

SEARCH.  Simulated annealing over the sets S_ij, with cost = number of vertices left unreached by the depth-D balls
from all (a+b) representatives.  Cost 0 means valid.  Candidate groups are non-abelian metacyclic groups and small
products, with order near 1000 (two orbits per side, n = 4N) and near 670 (three orbits per side, n = 6N).  Every
returned graph is checked with lib.is_valid.  If nothing is found, a precomputed valid Haar graph (n = 3582) is
returned, and the trivial graph is the final fallback.
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1); identity is element 0."""
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
    """AGL(1, q) for a prime power q: maps t -> a*t + b.  Identity is element 0."""
    F = lib.GF(q)
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in range(1, q) if (b, a) != (0, 1)], dtype=np.int64)
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


# ------------------------------------------------------------------------------------ multi-orbit lift

def lift_nbr(MT, inv, a, b, S, d):
    """Neighbour array (n x d) of the lift. A-orbit i vertex g is i*N+g; B-orbit j vertex h is (a+j)*N+h.
    Edge (i, g) ~ (j, s*g) for s in S[(i, j)]."""
    N = MT.shape[0]
    nbr = np.empty((N * (a + b), d), dtype=np.int64)
    cA = [0] * a
    cB = [0] * b
    for (i, j), arr in S.items():
        for s in arr:
            s = int(s)
            nbr[i * N:(i + 1) * N, cA[i]] = (a + j) * N + MT[s]
            cA[i] += 1
            nbr[(a + j) * N:(a + j + 1) * N, cB[j]] = i * N + MT[int(inv[s])]
            cB[j] += 1
    return nbr


def cost_of(nbr, N, T, D):
    """Total number of vertices not reached within distance D from each of the T orbit representatives."""
    n = nbr.shape[0]
    total = 0
    for t in range(T):
        s0 = t * N
        vis = np.zeros(n, dtype=bool)
        vis[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(D):
            m = np.zeros(n, dtype=bool)
            m[nbr[front].ravel()] = True
            m &= ~vis
            if not m.any():
                break
            vis |= m
            front = np.flatnonzero(m)
        total += n - int(np.count_nonzero(vis))
    return total


def anneal(MT, inv, a, b, M, d, deadline, rng, D=5, Temp=1.0, patience=2500):
    """Simulated annealing over the sets S_ij. Returns the S dict with cost 0, or None at the deadline."""
    N = MT.shape[0]
    T = a + b
    cells = [(i, j) for i in range(a) for j in range(b) if M[i][j] > 0]

    def fresh():
        return {c: rng.choice(N, M[c[0]][c[1]], replace=False).astype(np.int64) for c in cells}

    S = fresh()
    cur = cost_of(lift_nbr(MT, inv, a, b, S, d), N, T, D)
    best, since = cur, 0
    while True:
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            return None
        c = cells[int(rng.integers(len(cells)))]
        k = int(rng.integers(M[c[0]][c[1]]))
        x = int(rng.integers(N))
        arr = S[c]
        if x in arr:
            continue
        old = int(arr[k])
        arr[k] = x
        new = cost_of(lift_nbr(MT, inv, a, b, S, d), N, T, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / Temp):
            cur = new
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            arr[k] = old
            since += 1
        if since > patience:
            S = fresh()
            cur = cost_of(lift_nbr(MT, inv, a, b, S, d), N, T, D)
            best, since = cur, 0


def lift_edges(MT, inv, a, b, S, d):
    """Edge list of the lift for S (A-vertices have smaller ids than B-vertices, so each edge is listed once)."""
    nbr = lift_nbr(MT, inv, a, b, S, d)
    n = nbr.shape[0]
    edges = []
    for v in range(n):
        for u in nbr[v]:
            u = int(u)
            if u > v:
                edges.append((v, u))
    return n, edges


# --------------------------------------------------------------------------------- candidate families

PAT2 = [
    [[5, 5], [5, 5]],
    [[6, 4], [4, 6]],
    [[7, 3], [3, 7]],
]
PAT3 = [
    [[4, 3, 3], [3, 4, 3], [3, 3, 4]],
    [[4, 3, 3], [3, 3, 4], [3, 4, 3]],
    [[5, 3, 2], [2, 5, 3], [3, 2, 5]],
]


def candidate_groups(k):
    """List of (label, builder, group order) for the family with k orbits per side."""
    out = []
    if k == 2:
        lo, hi = 1001, 1041
        extra = [
            ("heis5xZ8", lambda: group_times_cyclic(group_heis(5), 8), 1000),
            ("sl2_5xZ9", lambda: group_times_cyclic(group_sl2(5), 9), 1080),
        ]
    else:
        lo, hi = 667, 701
        extra = [
            ("heis3xZ25", lambda: group_times_cyclic(group_heis(3), 25), 675),
            ("sl2_3xZ28", lambda: group_times_cyclic(group_sl2(3), 28), 672),
            ("agl7xZ16", lambda: group_times_cyclic(group_agl(7), 16), 672),
        ]
    out.extend(extra)
    meta = []
    for N in range(lo, hi):
        for kk in range(2, N):
            if N % kk:
                continue
            m = N // kk
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1:
                    meta.append((f"meta{m}x{kk}l{lam}",
                                 (lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam)), N))
                    break
    out.extend(meta[:12])
    return out


def task_list():
    """Interleaved (label, builder, a, M) tasks from both families."""
    fam2 = [(lab, bld, 2, pat) for lab, bld, _ in candidate_groups(2) for pat in PAT2[:2]]
    fam3 = [(lab, bld, 3, pat) for lab, bld, _ in candidate_groups(3) for pat in PAT3[:2]]
    out = []
    for x, y in itertools.zip_longest(fam2, fam3):
        if x is not None:
            out.append(x)
        if y is not None:
            out.append(y)
    return out


# ------------------------------------------------------------------------------------- top level

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


def run_multi(d, D, seed, time_limit):
    """Round-robin anneal over the task list until a valid lift is found or the search budget ends."""
    t0 = time.monotonic()
    deadline = t0 + 0.70 * time_limit
    slice_len = 6.0
    rng = np.random.default_rng(seed)
    for label, builder, a, M in task_list():
        now = time.monotonic()
        if now >= deadline:
            break
        if any(sum(row) != d for row in M) or any(sum(M[i][j] for i in range(a)) != d for j in range(a)):
            continue
        try:
            MT, inv = builder()
            S = anneal(MT, inv, a, a, M, d, min(deadline, now + slice_len), rng, D)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, edges = lift_edges(MT, inv, a, a, S, d)
        except Exception:
            continue
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


# ======================================================================================== cell: d10D5
TARGET = (10, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

FALLBACK_BUILDER = lambda: group_meta(199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run_multi(d, D, seed, time_limit)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = FALLBACK_BUILDER()
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
