"""Bipartite degree-diameter search for d=6, D=5, with a new construction and the Haar-graph fallback.

NEW CONSTRUCTION (tried first).  A voltage lift over a finite group G with a small base graph of t vertices per
side.  Blocks A_0..A_{t-1} and B_0..B_{t-1}, each a copy of G.  For each block pair (i, j) there is a set of
m_ij distinct group elements D_ij, and the edges are (A_i, x) ~ (B_j, x*s) for s in D_ij.  Row and column sums of
m are all d = 6, so the graph is bipartite, 6-regular, and has 2tN vertices.  Left multiplication by any h in G
is an automorphism that fixes every block, so the diameter is at most 5 iff every block representative (A_i, e),
(B_j, e) reaches all vertices within 5 steps.  The cost is the number of unreached vertices summed over these 2t
sources.  Orders are chosen so that 2tN >= 686, so any valid graph found here beats the record 684.

HAAR SEARCH (parent, kept as the safe path).  The successive-halving Haar search from the parent program runs
after the lift search, with the remaining time.  Its FALLBACK is always checked with lib.is_valid.

Every returned graph is verified with lib.is_valid before it is returned.
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^*."""
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


# ------------------------------------------------------------------------- Haar search (parent code)

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
    """Successive halving over the plan's Haar groups; returns a checked graph or the fallback."""
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


# ------------------------------------------------------------------- NEW: group voltage lifts, t per side

def _nbr(MT, inv, t, darts, d):
    """Neighbour array (2tN x d).  Block A_i is rows i*N.., block B_j is rows (t+j)*N.."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((2 * t * N, d), dtype=np.int64)
    fillA = [0] * t
    fillB = [0] * t
    for (i, j), arr in darts.items():
        for s in arr:
            s = int(s)
            nbr[i * N:(i + 1) * N, fillA[i]] = (t + j) * N + MT[g, s]
            fillA[i] += 1
            nbr[(t + j) * N:(t + j + 1) * N, fillB[j]] = i * N + MT[g, int(inv[s])]
            fillB[j] += 1
    return nbr


def _lift_cost(nbr, N, t, D):
    """Unreached vertices summed over the 2t block representatives (block b, element e)."""
    n = nbr.shape[0]
    tot = 0
    for b in range(2 * t):
        src = b * N
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nx = nbr[front].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            front = nx
        tot += n - int(seen.sum())
    return tot


def _lift_edges(MT, inv, t, darts, d):
    N = MT.shape[0]
    nbr = _nbr(MT, inv, t, darts, d)
    edges = []
    for r in range(t * N):
        for b in nbr[r]:
            edges.append((r, int(b)))
    return 2 * t * N, edges


def _random_darts(mult, N, rng):
    t = len(mult)
    return {(i, j): np.asarray(rng.choice(N, mult[i][j], replace=False), dtype=np.int64)
            for i in range(t) for j in range(t) if mult[i][j] > 0}


def _mutate(darts, N, rng):
    keys = list(darts.keys())
    key = keys[int(rng.integers(len(keys)))]
    arr = darts[key]
    k = int(rng.integers(len(arr)))
    taken = set(int(v) for v in arr)
    x = int(rng.integers(N))
    while x in taken:
        x = int(rng.integers(N))
    new = arr.copy()
    new[k] = x
    nd = dict(darts)
    nd[key] = new
    return nd


def _lift_slice(st, rng, end, D, d):
    N, t = st["N"], st["t"]
    while time.monotonic() < end and st["best"] > 0:
        if st["darts"] is None:
            st["darts"] = _random_darts(st["mult"], N, rng)
            st["cur"] = _lift_cost(_nbr(st["MT"], st["inv"], t, st["darts"], d), N, t, D)
            st["since"] = 0
            if st["cur"] < st["best"]:
                st["best"], st["bestD"] = st["cur"], st["darts"]
            if st["cur"] == 0:
                return
        nd = _mutate(st["darts"], N, rng)
        c = _lift_cost(_nbr(st["MT"], st["inv"], t, nd, d), N, t, D)
        delta = c - st["cur"]
        if delta <= 0 or rng.random() < math.exp(-delta / 1.0):
            st["darts"], st["cur"] = nd, c
            if c < st["best"]:
                st["best"], st["bestD"], st["since"] = c, nd, 0
                if c == 0:
                    return
        st["since"] += 1
        if st["since"] > 2000:
            st["darts"] = None


def _lift_specs():
    specs = []
    # t = 2: 4N vertices, need N >= 172
    for mult in ([[3, 3], [3, 3]], [[4, 2], [2, 4]]):
        for _name, N, m, k, lam in metacyclic_candidates(172, 200, 6):
            specs.append((mult, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    # t = 3: 6N vertices, need N >= 115
    for mult in ([[2, 2, 2], [2, 2, 2], [2, 2, 2]], [[3, 2, 1], [2, 2, 2], [1, 2, 3]]):
        for _name, N, m, k, lam in metacyclic_candidates(115, 130, 6):
            specs.append((mult, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return specs


def lift_search(d, D, seed, deadline):
    """Successive halving over group voltage lifts.  Returns a verified (n, edges) or None."""
    rng = np.random.default_rng(seed + 7919)
    alive = []
    for mult, builder in _lift_specs():
        if time.monotonic() >= deadline:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        alive.append({"mult": mult, "t": len(mult), "MT": MT, "inv": inv,
                      "N": MT.shape[0], "darts": None, "bestD": None,
                      "cur": None, "best": 10 ** 9, "since": 0})

    slice_t = 0.4
    while alive and time.monotonic() < deadline:
        for st in alive:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_t)
            try:
                _lift_slice(st, rng, end, D, d)
            except Exception:
                st["best"] = 10 ** 9
                continue
            if st["best"] == 0 and st["bestD"] is not None:
                try:
                    n, edges = _lift_edges(st["MT"], st["inv"], st["t"], st["bestD"], d)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
                except Exception:
                    pass
                # Invalid despite cost 0 (should not happen): restart this spec.
                st["best"], st["darts"], st["bestD"] = 10 ** 9, None, None
        alive.sort(key=lambda s: s["best"])
        if len(alive) > 1:
            alive = alive[:max(1, (len(alive) + 1) // 2)]
        slice_t *= 2
    return None


# ======================================================================================== cell: d6D5
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
    budget = 0.8 * time_limit
    try:
        got = lift_search(d, D, seed, t0 + 0.5 * budget)
        if got is not None:
            n, edges = got
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass
    remaining = max(1.0, budget - (time.monotonic() - t0))
    return run(d, D, seed, remaining / 0.8, PLAN, FALLBACK)
