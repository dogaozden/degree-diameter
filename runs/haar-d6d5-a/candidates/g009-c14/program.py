"""Voltage-lift search for the d=6, D=5 target, with the Haar search kept as a second stage.

NEW CONSTRUCTION (stage 1).  A bipartite base multigraph with two A-vertices and two B-vertices,
each vertex carrying 6 darts (row and column sums 6).  Each dart (A_i, B_j, g) lifts over a group G of
order N to the edges (A_i, x) ~ (B_j, x*g).  The lift is 6-regular and bipartite with 4N vertices.

Left multiplication by any h in G is an automorphism that fixes each fiber, so every vertex is
equivalent to one of the four base representatives (A_0, e), (A_1, e), (B_0, e), (B_1, e).  The lift
therefore has diameter at most 5 iff those four BFS trees reach all 4N vertices within 5 steps.  That
makes the cost cheap to evaluate: a few vectorised BFS passes per move.  Simulated annealing moves one
voltage at a time, and voltages inside a pair are kept distinct so the graph stays simple.

Stage 2 keeps the Haar-graph search from the parent (order >= 343 beats the record).  A fallback
Haar graph and a trivial graph guarantee a valid return.  Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)

# Multiplicity patterns k[i][j] for darts between A_i and B_j.  Row and column sums are 6.
PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
]


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Table of a group given by coordinates (element 0 is the identity) and a vectorised product."""
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
    """GF(q) x| C_k (default AGL(1, q))."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
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


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one per (m, k), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((f"Z_{m} x| Z_{k} (lam={lam}), order {N}", N, m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


# ------------------------------------------------------------------ stage 1: non-Haar voltage lifts

def lift_nb(MT, inv, darts):
    """Neighbour array (4N x 6) of the lift.  Vertices: A_i = i*N + x (i = 0, 1), B_j = (2+j)*N + y."""
    N = MT.shape[0]
    x = np.arange(N)
    nb = np.zeros((4 * N, 6), dtype=np.int64)
    cA = [0, 0]
    cB = [0, 0]
    for i, j, g in darts:
        nb[i * N:(i + 1) * N, cA[i]] = (2 + j) * N + MT[x, g]
        cA[i] += 1
        nb[(2 + j) * N:(3 + j) * N, cB[j]] = i * N + MT[x, inv[g]]
        cB[j] += 1
    return nb


def lift_cost(nb, N, D=5):
    """Number of (base representative, vertex) pairs not reached within D steps.  0 means diameter <= D."""
    n = 4 * N
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def lift_search(MT, inv, pattern, deadline, rng, patience=6000, T=1.5):
    """Simulated annealing over the voltages of one pattern.  Returns (V, cost), V None if no time."""
    N = MT.shape[0]
    struct = [(i, j) for i in range(2) for j in range(2) for _ in range(pattern[i][j])]
    E = len(struct)
    slots = {p: [u for u in range(E) if struct[u] == p] for p in set(struct)}

    def build(V):
        return [(struct[t][0], struct[t][1], int(V[t])) for t in range(E)]

    def fresh():
        V = np.zeros(E, dtype=np.int64)
        for idx in slots.values():
            V[idx] = rng.choice(N, len(idx), replace=False)
        return V

    best_V, best_c = None, 10 ** 9
    while time.monotonic() < deadline:
        V = fresh()
        c = lift_cost(lift_nb(MT, inv, build(V)), N)
        if c == 0:
            return V, 0
        stall = 0
        while time.monotonic() < deadline and stall < patience:
            t = int(rng.integers(E))
            used = set(int(V[u]) for u in slots[struct[t]])
            v = int(rng.integers(N))
            while v in used:
                v = int(rng.integers(N))
            V2 = V.copy()
            V2[t] = v
            c2 = lift_cost(lift_nb(MT, inv, build(V2)), N)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                V, c = V2, c2
                if c == 0:
                    return V, 0
            stall += 1
            if c < best_c:
                best_c, best_V = c, V.copy()
                stall = 0
    return best_V, best_c


def lift_graph(MT, inv, pattern, V):
    """The 4N-vertex lift for voltages V (A-vertex ids 0..2N-1, B-vertex ids 2N..4N-1)."""
    N = MT.shape[0]
    struct = [(i, j) for i in range(2) for j in range(2) for _ in range(pattern[i][j])]
    darts = [(struct[t][0], struct[t][1], int(V[t])) for t in range(len(struct))]
    nb = lift_nb(MT, inv, darts)
    edges = [(a, int(b)) for a in range(2 * N) for b in nb[a]]
    return 4 * N, edges


def lift_groups():
    """Groups of order just above 171 (a lift of order 4N beats the record 684 when N >= 172)."""
    out = [(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
           for _name, _N, m, k, lam in metacyclic_candidates(172, 190, 7)]
    out.append(lambda: group_times_cyclic(group_agl(5), 9))   # order 180
    return out


# ------------------------------------------------------------------------ stage 2: Haar search (parent)

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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Haar connection-set search with restarts.  Returns (S, cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

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
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def haar_plan():
    """Non-abelian groups of order 342..372 for the Haar search."""
    plan = [
        lambda: group_heis(7),                                  # order 343
        lambda: group_times_cyclic(group_agl(9), 5),            # order 360
        lambda: group_times_cyclic(group_heis(3), 13),          # order 351
    ]
    for _name, _N, m, k, lam in metacyclic_candidates(342, 372, 6):
        plan.append(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
    return plan


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def trivial(d, D):
    """Always-valid small graph for other (d, D) cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    total = 0.85 * time_limit
    end_all = t0 + total
    end1 = t0 + 0.62 * total
    rng = np.random.default_rng(seed)

    # Stage 1: 2+2 voltage lifts over non-abelian groups of order 172..190 (or 180).
    groups = lift_groups()
    for gi, builder in enumerate(groups):
        now = time.monotonic()
        if now >= end1:
            break
        end = now + (end1 - now) / (len(groups) - gi)
        pattern = PATTERNS[gi % len(PATTERNS)]
        try:
            MT, inv = builder()
            V, c = lift_search(MT, inv, pattern, end, rng)
        except Exception:
            continue
        if V is not None and c == 0:
            try:
                n, edges = lift_graph(MT, inv, pattern, V)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass

    # Stage 2: Haar search over groups of order 342..372 (order >= 343 beats the record).
    plan = haar_plan()
    for pi, builder in enumerate(plan):
        now = time.monotonic()
        if now >= end_all:
            break
        end = now + (end_all - now) / (len(plan) - pi)
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g

    # Fallback: a valid smaller Haar graph, then the trivial graph.
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
