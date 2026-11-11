"""Bipartite degree-diameter search for d=6, D=5.

Two constructions are tried for the target case, in order:
  1. NEW: multi-orbit voltage lifts. The base graph has two A-orbits and two B-orbits joined by
     a 6-regular multiplicity matrix. Each base dart carries a voltage in a metacyclic group G of
     order N, giving 4N vertices. Left multiplication is an automorphism that is transitive on each
     orbit, so the diameter check needs only four BFS roots, (orbit, identity). Every result is
     checked with lib.is_valid.
  2. PARENT: the Haar-graph search (unchanged), used as the safe fallback.
Other (d, D) cases return a small always-valid graph.
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


# ============================================================ NEW: multi-orbit voltage lifts (d=6, D=5)

LIFT_MATRICES = [[[3, 3], [3, 3]], [[4, 2], [2, 4]], [[2, 4], [4, 2]], [[5, 1], [1, 5]]]


def lift_candidates(lo, hi, cap):
    """Non-abelian metacyclic groups of order lo..hi (up to 2 per (m, k)), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    found += 1
                    if found >= 2:
                        break
    return out[:cap]


def make_darts(blocks, V):
    """Darts (i, j, voltage) for base blocks (i, j) with voltages V."""
    return [(i, j, int(V[b])) for b, (i, j) in enumerate(blocks)]


def lift_nbr(MT, darts, N):
    """Neighbour table (4N x d). A_i = vertex i*N + x (i in {0,1}), B_j = vertex (2+j)*N + y.
    Dart (i, j, g) joins (A_i, x) to (B_j, x*g) for all x in G."""
    x = np.arange(N, dtype=np.int64)
    srcs, dsts = [], []
    for i, j, g in darts:
        s = i * N + x
        t = (2 + j) * N + MT[:, g].astype(np.int64)
        srcs.append(s)
        dsts.append(t)
    s = np.concatenate(srcs)
    t = np.concatenate(dsts)
    src = np.concatenate([s, t])
    dst = np.concatenate([t, s])
    order = np.argsort(src, kind="stable")
    return dst[order].reshape(4 * N, -1)


def lift_cost(MT, darts, N, D):
    """Unreached (source, vertex) pairs within distance D, over the four orbit roots (u*N)."""
    nbr = lift_nbr(MT, darts, N)
    n = 4 * N
    R = np.zeros((n, 4), dtype=bool)
    R[np.arange(4) * N, np.arange(4)] = True
    for _ in range(D):
        R = R | R[nbr].any(axis=1)
    return 4 * n - int(R.sum())


def lift_edges(MT, darts, N):
    """Explicit (n, edges) of the lift."""
    x = np.arange(N, dtype=np.int64)
    edges = []
    for i, j, g in darts:
        a_ids = i * N + x
        b_ids = (2 + j) * N + MT[:, g].astype(np.int64)
        edges.extend((int(a), int(b)) for a, b in zip(a_ids, b_ids))
    return 4 * N, edges


def lift_search(MT, N, rng, deadline, d, D, K=16, T=1.5, patience=1500):
    """Simulated-annealing-style search over voltages, with restarts. Returns darts with cost 0, or None."""
    while time.monotonic() < deadline:
        M = LIFT_MATRICES[int(rng.integers(len(LIFT_MATRICES)))]
        blocks = [(i, j) for i in range(2) for j in range(2) for _ in range(M[i][j])]
        nd = len(blocks)
        V = np.zeros(nd, dtype=np.int64)
        for i in range(2):
            for j in range(2):
                idx = [b for b, bl in enumerate(blocks) if bl == (i, j)]
                if idx:
                    V[idx] = rng.choice(N, len(idx), replace=False)
        cur = lift_cost(MT, make_darts(blocks, V), N, D)
        if cur == 0:
            return make_darts(blocks, V)
        rbest, stuck = cur, 0
        while time.monotonic() < deadline and stuck < patience:
            b = int(rng.integers(nd))
            i, j = blocks[b]
            same = [int(V[c]) for c, bl in enumerate(blocks) if bl == (i, j) and c != b]
            bc, bg = None, None
            for _ in range(K):
                g = int(rng.integers(N))
                if g in same:
                    continue
                W = V.copy()
                W[b] = g
                c = lift_cost(MT, make_darts(blocks, W), N, D)
                if bc is None or c < bc:
                    bc, bg = c, g
            stuck += 1
            if bc is None:
                continue
            delta = bc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                V[b] = bg
                cur = bc
                if cur < rbest:
                    rbest, stuck = cur, 0
                if cur == 0:
                    return make_darts(blocks, V)
    return None


def lift_phase(deadline, rng, d, D):
    """Try groups of order 172..200; return the largest checked valid lift as (n, edges), or None."""
    cands = lift_candidates(172, 200, 20)
    best = None
    for idx, (N, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, _ = group_meta(m, k, lam)
            darts = lift_search(MT, N, rng, slice_end, d, D)
        except Exception:
            continue
        if darts is None:
            continue
        try:
            n, edges = lift_edges(MT, darts, N)
        except Exception:
            continue
        if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
            best = (n, edges)
    return best


# ============================================================ PARENT: Haar-graph search (unchanged)

def cover_dummy():
    return None


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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group, with restarts when stuck.
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


# ======================================================================================== dispatch
TARGET = (6, 5)

PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]

for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    # Phase 1 (new construction): multi-orbit voltage lifts, about 40% of the budget.
    best = None
    try:
        best = lift_phase(t0 + 0.40 * time_limit, rng, d, D)
    except Exception:
        best = None
    if best is not None:
        n, edges = best
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # Phase 2 (safe fallback): the parent Haar-graph search with the remaining budget.
    remaining = max(end_all - time.monotonic(), 1.0)
    try:
        return run(d, D, seed, remaining / 0.8, PLAN, FALLBACK)
    except Exception:
        return trivial(d, D)
