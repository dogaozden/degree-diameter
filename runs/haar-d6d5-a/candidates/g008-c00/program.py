"""Two-orbit voltage lifts plus Haar-graph search for the bipartite degree-diameter problem, d=6, D=5.

PHASE 1 (new construction).  Base multigraph: two A-vertices and two B-vertices, with M[i][j] darts from A_i to
B_j (row and column sums 6, so the lift is 6-regular).  Each dart carries a voltage g in a group G, and the lift
joins (x, A_i) to (x*g, B_j).  The lift has 4|G| vertices, is bipartite, and is 6-regular.  Voltages are searched
by simulated annealing, with the cost equal to the number of vertex pairs at distance > 5 (lib-style bitmask BFS).
Any zero-cost lift with 4|G| > 684 is checked with lib.is_valid and kept.

PHASE 2 (Haar graphs).  The earlier Haar-graph search over non-abelian groups of order 342..372 runs on the
remaining time.

A valid smaller Haar graph is computed first, so a valid graph is always available. The largest checked graph wins.
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------- two-orbit voltage lifts

MATRICES = [((3, 3), (3, 3)), ((4, 2), (2, 4)), ((2, 4), (4, 2)), ((5, 1), (1, 5))]
_popcount = getattr(int, "bit_count", None) or (lambda x: bin(x).count("1"))


def _bad_count(adj, n, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - _popcount(r) for r in reach) // 2


def _lift_adj(N, volts, MTl):
    """Adjacency of the 4N-vertex lift. A_i vertex x -> i*N + x; B_j vertex y -> 2N + j*N + y."""
    adj = [[] for _ in range(4 * N)]
    for i in range(2):
        for j in range(2):
            for g in volts[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = 2 * N + j * N + MTl[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _lift_edges(N, volts, MTl):
    edges = []
    for i in range(2):
        for j in range(2):
            for g in volts[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + MTl[x][g]))
    return 4 * N, edges


def _sample_volts(N, M, rng):
    return [[[int(v) for v in rng.choice(N, M[i][j], replace=False)] for j in range(2)] for i in range(2)]


def lift_search(MTl, N, deadline, rng, D=5, T=0.6, stall_limit=1500):
    """Anneal the 12 voltages of a two-orbit lift until every pair is within distance D.
    Returns the voltage assignment if cost 0 is reached, else None."""
    while time.monotonic() < deadline:
        M = MATRICES[int(rng.integers(len(MATRICES)))]
        volts = _sample_volts(N, M, rng)
        cur = _bad_count(_lift_adj(N, volts, MTl), 4 * N, D)
        if cur == 0:
            return volts
        stall = 0
        while time.monotonic() < deadline and stall < stall_limit:
            i = int(rng.integers(2))
            j = int(rng.integers(2))
            k = int(rng.integers(M[i][j]))
            new = int(rng.integers(N))
            if new in volts[i][j]:
                continue
            old = volts[i][j][k]
            volts[i][j][k] = new
            c = _bad_count(_lift_adj(N, volts, MTl), 4 * N, D)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                if cur == 0:
                    return volts
                stall = 0 if delta < 0 else stall + 1
            else:
                volts[i][j][k] = old
                stall += 1
    return None


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
    """Local search over d-subsets of the group, with restarts when stuck. Returns (best S, best cost)."""
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


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

# Groups for the two-orbit lift: 4|G| must exceed 684, so |G| >= 172.
LIFT_GROUPS = [
    ('Heis(3) x Z_7, order 189', lambda: group_times_cyclic(group_heis(3), 7)),
    ('AGL(1,8) x Z_4, order 224', lambda: group_times_cyclic(group_agl(8), 4)),
    ('Heis(5) x Z_2, order 250', lambda: group_times_cyclic(group_heis(5), 2)),
]
for _name, _N, _m, _k, _lam in metacyclic_candidates(172, 200, 12):
    LIFT_GROUPS.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

# Fixed non-abelian Haar families just above the threshold 342.
PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 10):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

# Valid smaller Haar graph (order 660), checked at run time; the guaranteed fallback.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    end_all = t0 + 0.80 * time_limit
    phase1_end = t0 + 0.55 * time_limit
    rng = np.random.default_rng(seed)

    best = None

    def consider(g):
        nonlocal best
        if g is not None and (best is None or g[0] > best[0]):
            best = g

    # Guaranteed valid fallback first.
    try:
        MT, _ = FALLBACK[0]()
        consider(checked(MT, FALLBACK[1], d, D))
    except Exception:
        pass

    # Phase 1: two-orbit voltage lifts over several groups, equal time each.
    groups = LIFT_GROUPS
    for idx, (name, builder) in enumerate(groups):
        now = time.monotonic()
        if now >= phase1_end:
            break
        end = now + (phase1_end - now) / (len(groups) - idx)
        try:
            MT, _ = builder()
            N = MT.shape[0]
            if 4 * N <= 684:
                continue
            MTl = MT.tolist()
            volts = lift_search(MTl, N, end, rng)
            if volts is not None:
                n, edges = _lift_edges(N, volts, MTl)
                if lib.is_valid(n, edges, d, D):
                    consider((n, edges))
        except Exception:
            continue

    # Phase 2: Haar-graph search over the remaining time.
    total_w = sum(w for *_, w in PLAN)
    for name, builder, S0, w in PLAN:
        now = time.monotonic()
        if now >= end_all:
            break
        end = now + (end_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            consider(checked(MT, S, d, D))
            if best is not None and best[0] > 684:
                break

    return best if best is not None else trivial(d, D)
