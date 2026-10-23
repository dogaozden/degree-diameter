"""Variant for d=6, D=5: voltage lifts of small bipartite base graphs over non-abelian groups.

Each candidate has 2 or 3 base vertices per side (order 2*k*|G| with |G| near 172 or 115), and every
base vertex has degree 6. Left multiplication by G is an automorphism of the lift, so the diameter is
at most 5 iff every base vertex's BFS ball of radius 5 from (u, e) covers all 2k|G| vertices. The cost
is the total number of uncovered vertices over the 2k base sources. Voltages are annealed to cost 0.
Any found graph is checked with lib.is_valid. If nothing is found in the lift phase, the parent's
Haar-group search runs, then its valid 660-vertex Haar fallback.
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
    """GF(q) x| C_k (default AGL(1, q))."""
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
    """Direct product of a table group (MT, inv) with Z_k."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------- Haar search (parent)

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
    """Annealing over d-subsets of the group. Returns (best S, best cost)."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
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
            if delta < 0:
                since = 0
        since += 1
        if since > patience:
            S = None
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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """Parent's Haar search over a plan of (name, builder, weight), then a checked fallback."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for _, _, w in plan)
    for name, builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
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


# ------------------------------------------------------------------- new: voltage lifts of small bases

def metacyclic(N, want):
    """Up to `want` non-abelian metacyclic (m, kk, lam) with m*kk = N."""
    out = []
    for kk in range(2, N + 1):
        if N % kk:
            continue
        m = N // kk
        if m < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1 % m:
                out.append((m, kk, lam))
                if len(out) >= want:
                    return out
    return out


def _dart_pairs(k, M):
    return [(a, b) for a in range(k) for b in range(k) for _ in range(M[a][b])]


def lift_edges(MT, k, pairs, volt, d, D):
    """Edges of the lift: dart (a, b, g) joins (a, x) to (k+b, x*g). Returns (n, edges) if valid, else None."""
    N = MT.shape[0]
    edges = []
    for i, (a, b) in enumerate(pairs):
        col = MT[:, volt[i]]
        for x in range(N):
            edges.append((a * N + x, (k + b) * N + int(col[x])))
    n = 2 * k * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def lift_search(MT, inv, k, M, pairs, d, D, deadline, rng):
    """Anneal the voltages of a lift until the BFS cost is 0. Returns the voltage list or None."""
    N = MT.shape[0]
    nd = len(pairs)
    inc = [[] for _ in range(2 * k)]
    for i, (a, b) in enumerate(pairs):
        inc[a].append((i, 0, k + b))
        inc[k + b].append((i, 1, a))
    if any(len(lst) != d for lst in inc):
        return None
    n_total = 2 * k * N
    pid = {}
    for i, p in enumerate(pairs):
        pid.setdefault(p, []).append(i)

    def build_nb(volt):
        NB = np.empty((n_total, d), dtype=np.int64)
        for u in range(2 * k):
            for t, (i, side, tgt) in enumerate(inc[u]):
                g = volt[i]
                mv = g if side == 0 else int(inv[g])
                NB[u * N:(u + 1) * N, t] = tgt * N + MT[:, mv]
        return NB

    def unreached(NB, src):
        seen = np.zeros(n_total, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = NB[fr].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            fr = nb
        return n_total - int(seen.sum())

    def cost(volt):
        NB = build_nb(volt)
        return sum(unreached(NB, u * N) for u in range(2 * k))

    def fresh():
        volt = [0] * nd
        for p, idxs in pid.items():
            vals = rng.choice(N, len(idxs), replace=False)
            for i, v in zip(idxs, vals):
                volt[i] = int(v)
        return volt

    T = 1.0
    while time.monotonic() < deadline:
        volt = fresh()
        cur = cost(volt)
        stale = 0
        while time.monotonic() < deadline and stale < 2000:
            if cur == 0:
                return volt
            i = int(rng.integers(nd))
            g = int(rng.integers(N))
            idxs = pid[pairs[i]]
            if any(volt[j] == g for j in idxs if j != i):
                continue
            old = volt[i]
            volt[i] = g
            c = cost(volt)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c
                stale = 0 if delta < 0 else stale + 1
            else:
                volt[i] = old
                stale += 1
        if cur == 0:
            return volt
    return None


def lift_phase(d, D, rng, deadline):
    M2 = [[3, 3], [3, 3]]
    M3 = [[2, 2, 2], [2, 2, 2], [2, 2, 2]]
    cfgs = []
    for k, M, Ns in [(2, M2, [172, 174, 176, 178, 180, 171]),
                     (3, M3, [115, 116, 117, 118, 120, 114])]:
        for N in Ns:
            for (m, kk, lam) in metacyclic(N, 2):
                cfgs.append((2 * k * N, k, M, N, (m, kk, lam)))
    # Smallest graph above the record first; the 684 ties go last.
    cfgs.sort(key=lambda c: (c[0] == 684, c[0]))

    for idx, (n, k, M, N, (m, kk, lam)) in enumerate(cfgs):
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.2:
            break
        slice_end = now + rem / (len(cfgs) - idx)
        try:
            MT, inv = group_meta(m, kk, lam)
            pairs = _dart_pairs(k, M)
            volt = lift_search(MT, inv, k, M, pairs, d, D, slice_end, rng)
            if volt is None:
                continue
            res = lift_edges(MT, k, pairs, volt, d, D)
            if res is not None:
                return res
        except Exception:
            continue
    return None


# ------------------------------------------------------------------------------- the program

PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), 3),
    ('Heis(7), order 343', lambda: group_heis(7), 2),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), 2),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), 2),
]

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.8 * time_limit
    rng = np.random.default_rng(seed)
    try:
        res = lift_phase(d, D, rng, t0 + 0.7 * budget)
        if res is not None:
            return res
    except Exception:
        pass
    return run(d, D, seed, 0.3 * time_limit, PLAN, FALLBACK)
