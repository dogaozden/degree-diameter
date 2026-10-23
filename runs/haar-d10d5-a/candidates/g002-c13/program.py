"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d (the connection set).  The Haar graph has
vertices (g, A) and (g, B) for g in G and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular
with 2|G| vertices.  Right multiplication by any h in G is an automorphism, so every A-vertex looks like (e, A)
and every B-vertex like (e, B).  Its diameter is at most 5 iff
        (S^-1 S)^2 = G   and   (S S^-1)^2 = G
(the left set covers the A side, the right set the B side).  Counting words, |G| <= 1 + d(d-1) + d(d-1)^3,
and in abelian groups many words coincide, so good examples live in non-abelian groups.
COST(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|) = number of group elements left uncovered; cost 0 = valid.

NEW IN THIS VERSION.  A substantially different construction is tried first for the target: a voltage lift
over a 2+2 orbit base.  Two A-orbits and two B-orbits, each of size N (a group order), with 2x2 cells of
CELL = 5 darts (each A-vertex and B-vertex has degree 10).  Dart (x, y, s) joins (g, x) to (g*s, y) for all g.
Left multiplication is an automorphism, so diameter <= 5 can be checked by 4 BFS runs from the identity of each
orbit, using a numpy frontier BFS over 4N vertices.  Annealing on the 20 voltages (distinct within each cell)
aims for cost 0 at 4N >= 4002 vertices (beats the record 4000).  Every candidate is checked with lib.is_valid.
If this fails, the program falls back to the original Haar-graph search and its checked smaller graph, so the
score is never 0 for a near miss.
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
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
    """GF(q) x| C_k: the maps t -> a*t + b on GF(q) with a in the subgroup of order k of GF(q)^* (default k = q-1,
    that is AGL(1, q)).  q a prime power (uses lib.GF).  The product is (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)   # x^-1 s, s^-1 x
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)   # x s^-1, s x^-1
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score EVERY single-slot replacement of S (all slots x all group elements).  Returns (best cost, best S)."""
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
    """Local search over d-subsets of the group.  With a start set S0: scan all its 1-swap neighbours first, then
    anneal from it, and restart from a perturbed S0 (half the time) or a random set when stuck.
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


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, seconds-weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
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
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================= NEW: 2+2 orbit voltage lift

CELL = 5     # darts per (A_x, B_y) cell
DEG = 10     # every base vertex has CELL*2 = 10 darts


def meta_candidates(lo, hi):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with order N = m*k in [lo, hi); returns (m, k, lam) tuples."""
    out = []
    for N in range(lo, hi):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
                    break
    return out


def lift_nbr(MT, inv, darts):
    """Neighbour array (4N, DEG). darts: int array (2, 2, CELL) of group indices. Vertex t*N+g:
    t = 0, 1 are A-orbits, t = 2, 3 are B-orbits. Dart (x, y, s): (g, x) ~ (g*s, y)."""
    N = MT.shape[0]
    g = np.arange(N)
    nbr = np.zeros((4, N, DEG), dtype=np.int64)
    sa = [0, 0]
    sb = [0, 0]
    for x in range(2):
        for y in range(2):
            for k in range(CELL):
                s = int(darts[x, y, k])
                nbr[x, :, sa[x]] = (2 + y) * N + MT[g, s]
                sa[x] += 1
                # B-vertex h of orbit y is adjacent to A-vertex g = h*s^-1 of orbit x.
                nbr[2 + y, :, sb[y]] = x * N + MT[g, inv[s]]
                sb[y] += 1
    return nbr.reshape(4 * N, DEG)


def lift_cost(nbr, N):
    """Number of (source orbit, vertex) pairs not reached within distance 5 from the identity of each orbit.
    Left multiplication is an automorphism, so this is zero iff the lift has diameter <= 5."""
    V = nbr.shape[0]
    total = 0
    for t in range(4):
        seen = np.zeros(V, dtype=bool)
        src = t * N
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(5):
            nb = nbr[frontier].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            frontier = nb
        total += V - int(seen.sum())
    return total


def lift_search(MT, inv, rng, deadline):
    """Anneal the 20 voltages (distinct within each cell). Returns (best darts, best cost)."""
    N = MT.shape[0]

    def fresh():
        dd = np.zeros((2, 2, CELL), dtype=np.int64)
        for x in range(2):
            for y in range(2):
                dd[x, y] = rng.choice(N, CELL, replace=False)
        return dd

    darts = fresh()
    cur = lift_cost(lift_nbr(MT, inv, darts), N)
    best, bestc = darts.copy(), cur
    since, T = 0, 2.0
    while bestc > 0 and time.monotonic() < deadline:
        x, y, k = int(rng.integers(2)), int(rng.integers(2)), int(rng.integers(CELL))
        old = int(darts[x, y, k])
        s = int(rng.integers(N))
        while s in darts[x, y]:
            s = int(rng.integers(N))
        darts[x, y, k] = s
        c = lift_cost(lift_nbr(MT, inv, darts), N)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if cur < bestc:
                best, bestc, since = darts.copy(), cur, 0
        else:
            darts[x, y, k] = old
        since += 1
        if since > 1500:
            darts = fresh()
            cur = lift_cost(lift_nbr(MT, inv, darts), N)
            since, T = 0, 2.0
    return best, bestc


def lift_graph(MT, inv, darts):
    """(n, edges) of the lift: A-vertices 0..2N-1, B-vertices 2N..4N-1, each edge listed once from the A side."""
    N = MT.shape[0]
    nbr = lift_nbr(MT, inv, darts)
    edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
    return 4 * N, edges


def bold_lift(d, D, seed, deadline):
    """Try 2+2 orbit lifts over several groups of order just above 1000. Returns a checked graph or None."""
    rng = np.random.default_rng(seed + 12345)
    cands = meta_candidates(1001, 1041)[:6]
    specs = [("meta", c) for c in cands] + [("heis", 11)]
    for idx, (kind, arg) in enumerate(specs):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(specs) - idx)
        try:
            MT, inv = group_meta(*arg) if kind == "meta" else group_heis(arg)
            darts, c = lift_search(MT, inv, rng, end)
        except Exception:
            continue
        if c == 0:
            try:
                n, edges = lift_graph(MT, inv, darts)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
    return None


# ======================================================================================== cell: d10D5
# Other group families just above the threshold 2000: SL(2,7) x Z_6 (2016), Heisenberg(7) x Z_6 (2058), AGL(1,13) x Z_13 (2028), AGL(1,16) x Z_9 (2160); annealing from random S.
TARGET = (10, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# (name, group builder, start set S0 or None, share of the time budget).  S0 = element indices of the group table.
PLAN = [
    ('SL(2,7) x Z_6, order 2016', lambda: group_times_cyclic(group_sl2(7), 6), None, 2),
    ('Heis(7) x Z_6, order 2058', lambda: group_times_cyclic(group_heis(7), 6), None, 2),
    ('AGL(1,13) x Z_13, order 2028', lambda: group_times_cyclic(group_agl(13), 13), None, 1),
    ('AGL(1,16) x Z_9, order 2160', lambda: group_times_cyclic(group_agl(16), 9), None, 1),
]

# Valid smaller Haar graph, checked at run time; used only when no search reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    try:
        # Bold phase: a different construction gets the first ~55% of the budget.
        res = bold_lift(d, D, seed, t0 + 0.55 * time_limit)
        if res is not None:
            return res
    except Exception:
        pass
    # Safe phase: the original Haar search, with a checked fallback that always returns a valid graph.
    remaining = 0.9 * time_limit - (time.monotonic() - t0)
    return run(d, D, seed, max(remaining, 0.5), PLAN, FALLBACK)
