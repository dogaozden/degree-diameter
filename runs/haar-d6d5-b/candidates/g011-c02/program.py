"""Diameter-5, degree-6 bipartite graphs: a new strategy in place of plain Haar annealing.

Two constructions are searched, and every result is checked with lib.is_valid.

1. Voltage lifts over a base graph with 4 vertices, K_{2,2} with each pair joined by 3 darts.
   A group G of order m gives 4m vertices. The lift is bipartite and 6-regular. Left multiplication
   by h is an automorphism, so diameter <= 5 holds iff a radius-5 BFS from each of the 4 base
   identities (u, e) reaches every vertex. The cost is the number of unreached vertices, summed
   over those 4 BFS runs. Voltages are annealed. With m = 171 this gives 684 vertices (the record);
   with m >= 172 it gives more.

2. Haar graphs over groups of order 342 (AGL(1,19), the record order), annealed as in the parent.

If nothing reaches cost 0 in time, the parent's valid smaller Haar graph is returned.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
BIG = 10 ** 9


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, identity index 0."""
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


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, identity index 0, order q(q-1)."""
    F = lib.GF(q)
    H = [a for a in range(1, q)]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


# ------------------------------------------------------------- Haar search (order-342 groups)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
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


def haar_search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, BIG
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
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
        since += 1
        if since > patience:
            S = None
    return best, bestc


def haar_graph_of(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ------------------------------------------------------- voltage lifts of a 4-vertex base

# Base graph: A-vertices 0,1 and B-vertices 2,3; every pair joined by 3 darts (K_{2,2} x 3).
PAIRS = [(0, 2), (0, 3), (1, 2), (1, 3)]


def lift_adjacency(MT, darts):
    """Neighbour table (4G, 6) of the lift, plus the edge endpoint arrays A, B.
    Returns (None, None, None) if the lift is not simple and 6-regular."""
    G = MT.shape[0]
    x = np.arange(G, dtype=np.int64)
    As, Bs = [], []
    for u, v, g in darts:
        As.append(u * G + x)
        Bs.append(v * G + MT[x, g].astype(np.int64))
    A = np.concatenate(As)
    B = np.concatenate(Bs)
    n = 4 * G
    src = np.concatenate([A, B])
    dst = np.concatenate([B, A])
    cnt = np.bincount(src, minlength=n)
    if not (cnt == 6).all():
        return None, None, None
    order = np.argsort(src, kind="stable")
    nb = dst[order].reshape(n, 6)
    s = np.sort(nb, axis=1)
    if (s[:, 1:] == s[:, :-1]).any():
        return None, None, None
    return nb, A, B


def lift_cost(nb, G):
    """Unreached-vertex count, summed over radius-5 BFS from each base identity (u, e)."""
    n = nb.shape[0]
    total = 0
    for u in range(4):
        s = u * G
        reached = np.zeros(n, dtype=bool)
        reached[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(5):
            nxt = nb[frontier].ravel()
            nxt = nxt[~reached[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            reached[nxt] = True
            frontier = nxt
        total += n - int(reached.sum())
    return total


def _darts(V):
    return [(u, v, int(V[p, k])) for p, (u, v) in enumerate(PAIRS) for k in range(3)]


def lift_anneal(MT, rng, deadline, temp=1.5, patience=3000):
    G = MT.shape[0]

    def evaluate(V):
        nb, _, _ = lift_adjacency(MT, _darts(V))
        if nb is None:
            return BIG
        return lift_cost(nb, G)

    def random_V():
        return np.array([rng.choice(G, 3, replace=False) for _ in PAIRS], dtype=np.int64)

    V = random_V()
    cur = evaluate(V)
    best, bestc = V.copy(), cur
    since = 0
    while bestc > 0 and time.monotonic() < deadline:
        p = int(rng.integers(4))
        k = int(rng.integers(3))
        g = int(rng.integers(G))
        if g in V[p]:
            continue
        old = V[p, k]
        V[p, k] = g
        c = evaluate(V)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            if c < bestc:
                best, bestc, since = V.copy(), c, 0
        else:
            V[p, k] = old
        since += 1
        if since > patience:
            V = random_V()
            cur = evaluate(V)
            since = 0
    return best, bestc


def lift_graph(MT, V):
    G = MT.shape[0]
    nb, A, B = lift_adjacency(MT, _darts(V))
    if nb is None:
        return None
    edges = list(zip(A.tolist(), B.tolist()))
    return 4 * G, edges


# ----------------------------------------------------------------- shared helpers

def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def checked_haar(MT, S, d, D):
    n, edges = haar_graph_of(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def checked_lift(MT, V, d, D):
    g = lift_graph(MT, V)
    if g is None:
        return None
    n, edges = g
    return g if lib.is_valid(n, edges, d, D) else None


# ------------------------------------------------------------------------------ plan

# (kind, name, group builder, weight).  Lifts over order-171 groups give 684 vertices (the record);
# order >= 172 gives more.  The Haar entry uses AGL(1,19), order 342, giving 684 as well.
PLAN = [
    ('lift', 'Z19:9 (lam 4), order 171', lambda: group_meta(19, 9, 4), 6),
    ('haar', 'AGL(1,19), order 342', lambda: group_agl(19), 3),
    ('lift', 'Z43:4 (lam 42), order 172', lambda: group_meta(43, 4, 42), 2),
    ('lift', 'Z19:9 (lam 7), order 171', lambda: group_meta(19, 9, 7), 2),
    ('lift', 'Z29:6 (lam 28), order 174', lambda: group_meta(29, 6, 28), 2),
]

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in PLAN)
    for kind, name, builder, w in PLAN:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            if kind == 'lift':
                V, c = lift_anneal(MT, rng, end)
                if c == 0:
                    g = checked_lift(MT, V, d, D)
                    if g is not None:
                        return g
            else:
                S, c = haar_search(MT, inv, d, end, rng)
                if S is not None and c == 0:
                    g = checked_haar(MT, S, d, D)
                    if g is not None:
                        return g
        except Exception:
            continue
    try:
        MT, inv = FALLBACK[0]()
        g = checked_haar(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    try:
        if (d, D) != TARGET:
            return trivial(d, D)
        return run(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
