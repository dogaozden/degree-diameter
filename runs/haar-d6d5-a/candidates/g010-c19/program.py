"""Mixed construction for the bipartite degree-diameter problem, d = 6, D = 5.

Two constructions are tried in order, each verified with lib.is_valid before it is returned:

1. Non-Haar voltage lifts. The base graph has p A-vertices and p B-vertices, with a multiplicity matrix M
   whose row and column sums are 6. Each base edge carries a set of distinct group voltages. The lift over a
   group G of order N has 2pN vertices, and a random-restart annealing search drives the diameter cost to zero.
   Right multiplication is an automorphism, so only one representative per vertex class needs a BFS. This is
   the new, bold part. Orders above 684 are only reachable here.
2. Haar graphs over non-abelian groups of order 342 to 372 (the parent's search), which reach the record 684.

If neither produces a verified graph, a verified smaller Haar graph is used. Every other (d, D) gets a small
verified graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k acting by affine maps (k = q-1 gives AGL(1, q))."""
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
    """Direct product of a table group with Z_k."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one per (m, k)."""
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


# ------------------------------------------------------------------------- Haar graphs (parent search)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X."""
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
    """Local search over d-subsets of the group with restarts. Returns (best S, best cost)."""
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
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """Haar graph for S if exactly valid, else None."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# --------------------------------------------------------------------- voltage lifts (new construction)

def lift_edges(MT, p, volts):
    """Lift of a base graph with p A-vertices and p B-vertices over the group MT.
    Base edge (i, j) with voltage s joins (g, A_i) to (s*g, B_j) for every g.
    A-vertex (i, g) has index i*N+g; B-vertex (j, h) has index p*N + j*N + h."""
    N = MT.shape[0]
    edges = []
    for i in range(p):
        for j in range(p):
            base_b = p * N + j * N
            for s in volts[i][j]:
                col = MT[s].tolist()
                for g in range(N):
                    edges.append((i * N + g, base_b + col[g]))
    return 2 * p * N, edges


def lift_cost(MT, p, volts, D):
    """Number of vertex pairs at distance > D, computed from one BFS per vertex class.
    Right multiplication is an automorphism, so each class is vertex-transitive; cost 0 iff the lift is valid."""
    N = MT.shape[0]
    n, edges = lift_edges(MT, p, volts)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    reps = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    total = 0
    for r in reps:
        seen = {r}
        frontier = [r]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            if not nxt:
                break
            frontier = nxt
        total += n - len(seen)
    return total


def lift_search(MT, p, M, D, deadline, rng, patience=600, temp=0.6):
    """Anneal the voltages of a lift with base multiplicity matrix M (row and column sums 6).
    Returns (best volts, best cost)."""
    N = MT.shape[0]
    cells = [(i, j) for i in range(p) for j in range(p) if M[i][j] > 0]

    def random_volts():
        return [[(rng.choice(N, M[i][j], replace=False).tolist() if M[i][j] > 0 else [])
                 for j in range(p)] for i in range(p)]

    def copy_volts(v):
        return [[list(v[i][j]) for j in range(p)] for i in range(p)]

    volts = random_volts()
    cur = lift_cost(MT, p, volts, D)
    best, bestc = copy_volts(volts), cur
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        i, j = cells[int(rng.integers(len(cells)))]
        k = int(rng.integers(M[i][j]))
        old = volts[i][j][k]
        choices = [x for x in range(N) if x not in volts[i][j]]
        volts[i][j][k] = choices[int(rng.integers(len(choices)))]
        c = lift_cost(MT, p, volts, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur < bestc:
                best, bestc, since = copy_volts(volts), cur, 0
        else:
            volts[i][j][k] = old
        since += 1
        if since > patience:
            volts = random_volts()
            cur = lift_cost(MT, p, volts, D)
            since = 0
    return best, bestc


# ----------------------------------------------------------------------------------------- plans

def trivial(d, D):
    """Small verified graph for cases this program does not target."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    cands.append(lambda: lib.haar_graph(d, range(d)))
    for make in cands:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 2, [(0, 1)]


# Voltage-lift tasks: (p, M, m, k, lam, name). Lift order is 2pN, so N >= 172 (p=2) or N >= 115 (p=3) beats 684.
LIFT_TASKS = []
for _name, _N, _m, _k, _lam in metacyclic_candidates(172, 180, 4):
    for _M in ([[3, 3], [3, 3]], [[4, 2], [2, 4]]):
        LIFT_TASKS.append((2, _M, _m, _k, _lam, _name))
for _name, _N, _m, _k, _lam in metacyclic_candidates(115, 122, 2):
    LIFT_TASKS.append((3, [[2, 2, 2], [2, 2, 2], [2, 2, 2]], _m, _k, _lam, _name))

# Haar plan: parent's fixed non-abelian families plus metacyclic groups of order 342..372.
HAAR_PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
    HAAR_PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

# Verified smaller Haar graph (order 660), used only if nothing above succeeds.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def timed_tasks(tasks, deadline, fn):
    """Run fn(task, end) on each task with an equal share of the remaining time; return the first non-None result."""
    for idx, task in enumerate(tasks):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(tasks) - idx)
        res = fn(task, end)
        if res is not None:
            return res
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)

    def try_lift(task, end):
        try:
            p, M, m, k, lam, _name = task
            MT, _inv = group_meta(m, k, lam)
            volts, c = lift_search(MT, p, M, D, end, rng)
            if c == 0:
                n, edges = lift_edges(MT, p, volts)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            pass
        return None

    def try_haar(item, end):
        try:
            _name, builder = item
            MT, inv = builder()
            S, c = search(MT, inv, d, None, end, rng)
            if S is not None and c == 0:
                return checked(MT, S, d, D)
        except Exception:
            pass
        return None

    g = timed_tasks(LIFT_TASKS, t0 + 0.38 * time_limit, try_lift)
    if g is not None:
        return g

    g = timed_tasks(HAAR_PLAN, t0 + 0.76 * time_limit, try_haar)
    if g is not None:
        return g

    try:
        MT, _inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
