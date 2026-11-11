"""Two-pronged search for the bipartite degree-diameter target (d=6, D=5).

Prong 1 (new): voltage lifts of a 2+2 base multigraph over metacyclic groups of order 172..180.
A lift has 4|G| vertices, which beats the record 684 for |G| >= 172. Right multiplication by G is an
automorphism, so the diameter is the maximum eccentricity over four representatives (a0,e), (a1,e),
(b0,e), (b1,e). Each side has connection sets of size 3 toward each base vertex of the other side,
giving degree 6. Local search minimises the number of vertices unreached within D steps.

Prong 2 (kept from the parent): Haar graphs over non-abelian groups, searched by annealing with
incremental cost. This reaches 684 and is the safe result.

Only a graph that passes lib.is_valid is returned. The larger valid result wins.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


TARGET = (6, 5)
TEMP = 2.0
PATIENCE = 4000


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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k, the maps t -> a*t + b with a in the order-k subgroup of GF(q)^*."""
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


# ============================================================ prong 1: voltage lifts of a 2+2 base

def _lift_adj(MTl, sets, N):
    """Adjacency lists of the lift. A-vertex (a,x) = a*N + x, B-vertex (b,y) = 2N + b*N + y."""
    adj = [[] for _ in range(4 * N)]
    for a in range(2):
        for b in range(2):
            for g in sets[a][b]:
                for x in range(N):
                    u = a * N + x
                    v = 2 * N + b * N + MTl[x][g]
                    adj[u].append(v)
                    adj[v].append(u)
    return adj


def _lift_cost(adj, n, reps, D):
    """Total number of vertices not reached within D steps from the four orbit representatives."""
    total = 0
    for r in reps:
        dist = [-1] * n
        dist[r] = 0
        frontier = [r]
        seen = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            seen += len(nxt)
            frontier = nxt
        total += n - seen
    return total


def _lift_edges(MTl, sets, N):
    edges = []
    for a in range(2):
        for b in range(2):
            for g in sets[a][b]:
                for x in range(N):
                    edges.append((a * N + x, 2 * N + b * N + MTl[x][g]))
    return edges


def _random_sets(N, rng):
    return [[rng.sample(range(N), 3) for _ in range(2)] for _ in range(2)]


def _lift_search(st, D, end, rng):
    """Anneal the connection sets of one group until cost 0 (returns sets) or the time runs out (returns None)."""
    N = st["N"]
    MTl = st["MTl"]
    n = 4 * N
    reps = [0, N, 2 * N, 3 * N]
    if st["sets"] is None:
        st["sets"] = _random_sets(N, rng)
        st["cur"] = _lift_cost(_lift_adj(MTl, st["sets"], N), n, reps, D)
        st["since"] = 0
    sets, cur = st["sets"], st["cur"]
    while time.monotonic() < end:
        if cur == 0:
            st["sets"], st["cur"] = sets, cur
            return sets
        if st["since"] > PATIENCE:
            sets = _random_sets(N, rng)
            cur = _lift_cost(_lift_adj(MTl, sets, N), n, reps, D)
            st["since"] = 0
            continue
        a, b, pos = rng.randrange(2), rng.randrange(2), rng.randrange(3)
        g = rng.randrange(N)
        if g in sets[a][b]:
            continue
        old = sets[a][b][pos]
        sets[a][b][pos] = g
        c = _lift_cost(_lift_adj(MTl, sets, N), n, reps, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
            cur = c
            if delta < 0:
                st["since"] = 0
        else:
            sets[a][b][pos] = old
        st["since"] += 1
    st["sets"], st["cur"] = sets, cur
    return sets if cur == 0 else None


def lift_phase(d, D, seed, deadline):
    """Round-robin search over lifts of metacyclic groups of order 172..180. Returns a checked (n, edges) or None."""
    rng = random.Random(seed)
    states = []
    for _name, N, m, k, lam in metacyclic_candidates(172, 180, 12):
        if time.monotonic() >= deadline:
            break
        try:
            MT, _ = group_meta(m, k, lam)
        except Exception:
            continue
        states.append({"N": N, "MTl": MT.tolist(), "sets": None, "cur": None, "since": 0})

    slice_t = 0.5
    while states and time.monotonic() < deadline:
        for st in states:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_t)
            sets = _lift_search(st, D, end, rng)
            if sets is not None:
                n = 4 * st["N"]
                edges = _lift_edges(st["MTl"], sets, st["N"])
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        slice_t *= 1.5
    return None


# ============================================================ prong 2: Haar graphs (parent search)

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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
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
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    states = []
    for name, builder, S0, w in plan:
        if time.monotonic() >= deadline_all:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        states.append({"MT": MT, "inv": inv, "best": S0, "bestc": None})

    slice_t = 0.5
    while states and time.monotonic() < deadline_all:
        for st in states:
            now = time.monotonic()
            if now >= deadline_all:
                break
            end = min(deadline_all, now + slice_t)
            try:
                S, c = search(st["MT"], st["inv"], d, st["best"], end, rng)
            except Exception:
                continue
            if S is None:
                continue
            if st["bestc"] is None or c < st["bestc"]:
                st["best"], st["bestc"] = S, c
            if c == 0:
                g = checked(st["MT"], S, d, D)
                if g is not None:
                    return g
        slice_t *= 1.5

    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ============================================================ plan for d6D5

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
    best = None

    # Prong 1: new voltage-lift search, aiming above the record 684.
    try:
        lift = lift_phase(d, D, seed, t0 + 0.30 * time_limit)
        if lift is not None:
            best = lift
            if lift[0] > 684:
                return lift
    except Exception:
        pass

    # Prong 2: Haar search for the rest of the budget (safe result, 684 when it succeeds).
    elapsed = time.monotonic() - t0
    remaining = 0.80 * time_limit - elapsed
    if remaining <= 0.5:
        if best is not None:
            return best
        return trivial(d, D)
    g = run(d, D, seed, remaining / 0.80, PLAN, FALLBACK)

    if best is not None and best[0] > g[0]:
        return best
    return g
