"""Two-phase search for the d=6, D=5 bipartite degree-diameter target.

PHASE 1 (new construction): lifts of a small base multigraph with P "A" and P "B" base vertices over a
finite group G, with circulant multiplicities c (each row and column sums to d). Vertices are (block, g) with
blocks 0..2P-1, so there are 2P|G| vertices. Edges are darts (i, j, v): (a_i, x) ~ (b_j, x*v). Left
multiplication by any h in G is an automorphism, so the diameter is at most 5 iff every one of the 2P block
representatives (block, e) reaches all vertices within 5 steps. The cost is the total number of unreached
(representative, vertex) pairs, computed with numpy BFS from those 2P sources. Voltages are annealed.

PHASE 2 (parent): the Haar-graph successive-halving search, given the remaining time.

Each phase's output is checked with lib.is_valid, and the largest valid graph is returned. Failure in any
phase falls back to the next, so the program always returns a valid graph.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1,q))."""
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


# ------------------------------------------------------------------------------------- Haar search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X."""
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


def run(d, D, seed, time_limit, plan, fallback):
    """Successive halving over the plan's Haar groups. Returns a valid graph (n, edges)."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    alive = []
    for _name, builder, S0, _w in plan:
        if time.monotonic() >= deadline_all:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        alive.append({"MT": MT, "inv": inv,
                      "S": None if S0 is None else np.array(S0, dtype=np.int32),
                      "c": 10 ** 9})

    slice_t = 0.5
    while alive and time.monotonic() < deadline_all:
        for e in alive:
            now = time.monotonic()
            if now >= deadline_all:
                break
            end = min(deadline_all, now + slice_t)
            try:
                S, c = search(e["MT"], e["inv"], d, e["S"], end, rng)
            except Exception:
                e["c"] = 10 ** 9
                continue
            if S is not None and c < e["c"]:
                e["S"], e["c"] = S, c
            if c == 0 and S is not None:
                g = checked(e["MT"], S, d, D)
                if g is not None:
                    return g
        alive.sort(key=lambda e: e["c"])
        if len(alive) > 1:
            alive = alive[:max(1, (len(alive) + 1) // 2)]
        slice_t *= 2

    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ============================================================ PHASE 1: multi-block group lifts (d=6, D=5)

LIFT_CONFIGS = [          # (P, circulant multiplicities c): block i to block j gets c[(j-i) % P] darts
    (2, (3, 3)),
    (2, (2, 4)),
    (3, (2, 2, 2)),
    (4, (2, 2, 1, 1)),
]
LIFT_RANGE = {2: (172, 200), 3: (115, 135), 4: (86, 100)}   # group orders giving > 684 vertices
D_LIFT = 5


def _lift_groups(lo, hi):
    """(name, order, builder) for candidate groups with lo <= order <= hi."""
    out = []
    for _name, N, m, k, lam in metacyclic_candidates(lo, hi, 8):
        out.append((_name, N, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    bases = [("Heis(3)", lambda: group_heis(3), 27),
             ("Heis(5)", lambda: group_heis(5), 125),
             ("AGL(1,5)", lambda: group_agl(5), 20),
             ("AGL(1,7)", lambda: group_agl(7), 42),
             ("AGL(1,8)", lambda: group_agl(8), 56),
             ("AGL(1,9)", lambda: group_agl(9), 72)]
    for base_name, base_builder, base_n in bases:
        for k in range(1, 9):
            N = base_n * k
            if lo <= N <= hi:
                out.append((f"{base_name} x Z_{k}", N,
                            (lambda b=base_builder, kk=k: group_times_cyclic(b(), kk))))
    return out


def _sample_darts(rng, P, c, n):
    darts = []
    for i in range(P):
        for j in range(P):
            k = c[(j - i) % P]
            for g in rng.choice(n, k, replace=False):
                darts.append((i, j, int(g)))
    return darts


def _nbr(MT, inv, P, darts, d=6):
    """Neighbour array (2P*n, d): block i*n+x for i<P are A-blocks, (P+j)*n+y are B-blocks."""
    n = MT.shape[0]
    X = np.arange(n)
    nbr = np.zeros((2 * P * n, d), dtype=np.int64)
    for i in range(P):
        ds = [(j, g) for (a, j, g) in darts if a == i]
        for t, (j, g) in enumerate(ds):
            nbr[i * n + X, t] = (P + j) * n + MT[X, g]
    for j in range(P):
        ds = [(i, g) for (i, b, g) in darts if b == j]
        for t, (i, g) in enumerate(ds):
            nbr[(P + j) * n + X, t] = i * n + MT[X, int(inv[g])]
    return nbr


def _lift_cost(nbr, P, n, D=D_LIFT):
    """Sum over the 2P block representatives of the number of vertices not within distance D."""
    N = 2 * P * n
    total = 0
    for b in range(2 * P):
        s = b * n
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = nbr[fr].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            vis[nb] = True
            fr = np.unique(nb)
        total += N - int(vis.sum())
    return total


def _lift_graph(nbr, P, n):
    N = 2 * P * n
    edges = [(u, int(nbr[u, t])) for u in range(P * n) for t in range(nbr.shape[1])]
    return N, edges


def _anneal(e, deadline, rng, d=6, D=D_LIFT):
    """Metropolis search over the darts of one candidate. Returns a validated (n, edges) or None."""
    MT, inv, P, n = e["MT"], e["inv"], e["P"], e["n"]
    if e["darts"] is None:
        e["darts"] = _sample_darts(rng, P, e["c"], n)
    darts = e["darts"]
    nbr = _nbr(MT, inv, P, darts, d)
    cur = _lift_cost(nbr, P, n, D)
    if cur < e["best_c"]:
        e["best_c"] = cur
    T = 0.5
    while time.monotonic() < deadline:
        if cur == 0:
            N, edges = _lift_graph(nbr, P, n)
            if lib.is_valid(N, edges, d, D):
                return N, edges
            e["dead"] = True
            return None
        t = int(rng.integers(len(darts)))
        i, j, _g = darts[t]
        used = {g2 for (a, b, g2) in darts if a == i and b == j}
        ng = int(rng.integers(n))
        if ng in used:
            continue
        nd = darts[:t] + [(i, j, ng)] + darts[t + 1:]
        nn = _nbr(MT, inv, P, nd, d)
        c2 = _lift_cost(nn, P, n, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            darts, nbr, cur = nd, nn, c2
            e["darts"] = darts
            if cur < e["best_c"]:
                e["best_c"] = cur
    e["c"] = e["best_c"]
    return None


def _lift_search(seed, deadline, d=6, D=D_LIFT):
    """Successive halving over all (P, c, group) candidates. Returns a validated (n, edges) or None."""
    rng = np.random.default_rng(seed + 1)
    entries = []
    for P, c in LIFT_CONFIGS:
        lo, hi = LIFT_RANGE[P]
        for name, N, builder in _lift_groups(lo, hi):
            entries.append({"name": name, "n": N, "P": P, "c": c, "builder": builder,
                            "MT": None, "inv": None, "darts": None,
                            "best_c": 10 ** 9, "dead": False})
    alive = list(entries)
    slice_t = 0.2
    while alive and time.monotonic() < deadline:
        for e in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            if e["dead"]:
                continue
            if e["MT"] is None:
                try:
                    e["MT"], e["inv"] = e["builder"]()
                    if e["MT"].shape[0] != e["n"]:
                        e["dead"] = True
                        continue
                except Exception:
                    e["dead"] = True
                    continue
            end = min(deadline, now + slice_t)
            try:
                res = _anneal(e, end, rng, d, D)
            except Exception:
                e["dead"] = True
                continue
            if res is not None:
                return res
            e["c"] = e["best_c"]
        alive = [e for e in alive if not e["dead"]]
        alive.sort(key=lambda e: e["best_c"])
        if len(alive) > 1:
            alive = alive[:max(1, (len(alive) + 1) // 2)]
        slice_t *= 2
    return None


# ================================================================================ target and plan
TARGET = (6, 5)

PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 14):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    total = 0.85 * time_limit
    best = None
    try:
        res = _lift_search(seed, t0 + 0.40 * total, d, D)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            best = res
    except Exception:
        best = None
    if best is not None and best[0] > 684:
        return best
    remain = t0 + total - time.monotonic()
    g2 = None
    if remain > 1.0:
        try:
            g2 = run(d, D, seed, remain / 0.8, PLAN, FALLBACK)
        except Exception:
            g2 = None
    candidates = [g for g in (best, g2) if g is not None]
    if not candidates:
        return trivial(d, D)
    return max(candidates, key=lambda g: g[0])
