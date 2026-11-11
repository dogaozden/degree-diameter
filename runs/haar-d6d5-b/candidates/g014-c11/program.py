"""Bipartite voltage lifts over small base graphs for d=6, D=5 (new construction), with the Haar-graph search kept as fallback.

NEW CONSTRUCTION.  Take a base bipartite multigraph with k vertices on each side and d darts at every base vertex
(multiplicities given by a sum of d random permutation matrices).  Give each dart a voltage in a finite group G of
order N, using distinct voltages for darts that share the same endpoints.  The lift has 2kN vertices and is
d-regular and bipartite.  Left multiplication by G is an automorphism that is regular on each fibre, so the diameter
is at most D iff every base representative (b, identity) reaches all vertices within D steps.  COST counts the
unreached vertices over the 2k representatives, and cost 0 means valid.  Orders are chosen so that 2kN >= 686,
which beats the record 684.

FALLBACK.  If the lift search fails, the earlier Haar-graph search runs for the remaining time.  Every returned
graph is checked with lib.is_valid, and a precomputed valid smaller Haar graph is the last resort.
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
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi, None]] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
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


# ------------------------------------------------------------------------------- Haar-graph search (fallback)

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


def guided_candidates(MT, inv, S, i, rng, n):
    N = MT.shape[0]
    rest = np.delete(S, i)
    ri = inv[rest]
    side = int(rng.integers(2))
    if side == 0:
        E = np.unique(MT[ri[:, None], rest[None, :]])
    else:
        E = np.unique(MT[rest[:, None], ri[None, :]])
    unc = np.flatnonzero(~_cover(MT, N, E))
    if len(unc) == 0:
        return None
    u = int(unc[rng.integers(len(unc))])
    e = E[rng.integers(len(E), size=n)]
    y = rest[rng.integers(len(rest), size=n)]
    o = rng.integers(2, size=n).astype(bool)
    f = rng.integers(2, size=n).astype(bool)
    t = np.where(o, MT[inv[e], u], MT[u, inv[e]])
    if side == 0:
        X = np.where(f, MT[y, t], MT[y, inv[t]])
    else:
        X = np.where(f, MT[inv[t], y], MT[t, y])
    return X.astype(np.int32)


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000, p_guided=0.6):
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
        X = None
        if rng.random() < p_guided:
            X = guided_candidates(MT, inv, S, i, rng, K)
        if X is None:
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


def meta_candidates(lo, hi, exclude, limit):
    out = []
    for N in range(hi, lo, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and (m, k, lam) not in exclude:
                    out.append((m, k, lam))
                    if len(out) >= limit:
                        return out
    return out


def run(d, D, seed, time_limit, plan, fallback):
    t0 = time.monotonic()
    deadline_all = t0 + 0.82 * time_limit
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


TARGET = (6, 5)

PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3),
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 2),
    ('Heis(7), order 343', lambda: group_heis(7), None, 2),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 2),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 2),
]


def _extra_plan():
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ------------------------------------------------------------------------- bipartite voltage lifts (new)

TEMP = 1.0
PATIENCE = 4000


def _meta_list(lo, hi, per_order=2):
    """Metacyclic (m, k2, lam) with lam != 1 and order N in [lo, hi], ascending in N."""
    out = []
    for N in range(lo, hi + 1):
        found = 0
        for k2 in range(2, N):
            if N % k2:
                continue
            m = N // k2
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k2, m) == 1:
                    out.append((m, k2, lam))
                    found += 1
                    if found >= per_order:
                        break
            if found >= per_order:
                break
    return out


def make_darts(k, d, rng):
    """Base multigraph: d random permutations give k*d darts, each base vertex has d darts out and d in."""
    src, dst = [], []
    for _ in range(d):
        perm = rng.permutation(k)
        for i in range(k):
            src.append(i)
            dst.append(int(perm[i]))
    return np.array(src, dtype=np.int64), np.array(dst, dtype=np.int64)


def init_volt(src, dst, N, rng):
    """Random voltages; darts sharing the same endpoints get distinct voltages (no multi-edges)."""
    hv = np.zeros(len(src), dtype=np.int64)
    for i, j in set(zip(src.tolist(), dst.tolist())):
        idx = np.flatnonzero((src == i) & (dst == j))
        hv[idx] = rng.choice(N, size=len(idx), replace=False)
    return hv


def build_nbr(MT, invv, k, N, src, dst, hv, d):
    """Neighbour array (2kN, d).  A-vertex i*N+x joins (k+j)*N + x*h; B-vertex (k+j)*N+y joins i*N + y*h^-1."""
    nb = np.empty((2 * k * N, d), dtype=np.int64)
    for i in range(k):
        idx = np.flatnonzero(src == i)
        nb[i * N:(i + 1) * N] = (k + dst[idx])[None, :] * N + MT[:, hv[idx]]
    for j in range(k):
        idx = np.flatnonzero(dst == j)
        nb[(k + j) * N:(k + j + 1) * N] = src[idx][None, :] * N + MT[:, invv[hv[idx]]]
    return nb


def bilift_cost(nb, N, k, D):
    """Sum over the 2k base representatives (b, identity) of the vertices NOT within distance D.
    Left multiplication is a fibre-regular automorphism, so 0 here means diameter <= D."""
    n_tot = 2 * k * N
    total = 0
    for b in range(2 * k):
        seen = np.zeros(n_tot, dtype=bool)
        s = b * N
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = np.unique(cand[~seen[cand]])
            if cand.size == 0:
                break
            seen[cand] = True
            front = cand
        total += n_tot - int(seen.sum())
    return total


def bilift_run(task, rng, deadline):
    """Anneal the voltages of one task until deadline.  Returns the voltage array if cost 0 is found, else None."""
    k, N, d, D = task['k'], task['N'], task['d'], task['D']
    MT, invv, src, dst, hv = task['MT'], task['invv'], task['src'], task['dst'], task['hv']
    cur = bilift_cost(build_nbr(MT, invv, k, N, src, dst, hv, d), N, k, D)
    task['best'] = min(task['best'], cur)
    if cur == 0:
        return hv.copy()
    since = 0
    while time.monotonic() < deadline:
        e = int(rng.integers(len(hv)))
        same = (src == src[e]) & (dst == dst[e])
        same[e] = False
        taken = set(hv[same].tolist())
        x = int(rng.integers(N))
        while x in taken:
            x = int(rng.integers(N))
        old = int(hv[e])
        hv[e] = x
        c = bilift_cost(build_nbr(MT, invv, k, N, src, dst, hv, d), N, k, D)
        if c == 0:
            return hv.copy()
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            if c < task['best']:
                task['best'] = c
                since = 0
        else:
            hv[e] = old
        since += 1
        if since > PATIENCE:
            hv[:] = init_volt(src, dst, N, rng)
            cur = bilift_cost(build_nbr(MT, invv, k, N, src, dst, hv, d), N, k, D)
            since = 0
            if cur == 0:
                return hv.copy()
    return None


def make_tasks(d, D, rng):
    """One task per (k, group): 2kN >= 686 vertices, so each valid lift beats the record 684."""
    tasks = []
    for k in (2, 3, 4, 5):
        Nmin = -(-343 // k)
        for m, k2, lam in _meta_list(Nmin, Nmin + 4, per_order=2)[:4]:
            try:
                MT, invv = group_meta(m, k2, lam)
            except Exception:
                continue
            N = m * k2
            src, dst = make_darts(k, d, rng)
            hv = init_volt(src, dst, N, rng)
            tasks.append(dict(k=k, N=N, d=d, D=D, MT=MT, invv=invv, src=src, dst=dst, hv=hv,
                              best=10 ** 9, dead=False))
    return tasks


def graph_from(task, hv, d, D):
    k, N = task['k'], task['N']
    nb = build_nbr(task['MT'], task['invv'], k, N, task['src'], task['dst'], hv, d)
    n = 2 * k * N
    a = np.repeat(np.arange(k * N, dtype=np.int64), d)
    edges = list(zip(a.tolist(), nb[:k * N].ravel().tolist()))
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def bilift_phase(d, D, rng, deadline):
    tasks = make_tasks(d, D, rng)
    if not tasks:
        return None
    slice_s = 0.5
    while time.monotonic() < deadline:
        live = [t for t in tasks if not t['dead']]
        if not live:
            break
        for task in live:
            now = time.monotonic()
            if now >= deadline:
                break
            hv = bilift_run(task, rng, min(deadline, now + slice_s))
            if hv is not None:
                g = graph_from(task, hv, d, D)
                if g is not None:
                    return g
                task['dead'] = True
        slice_s *= 1.5
    return None


# ======================================================================================== entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    total = max(2.0, 0.85 * time_limit - 1.0)
    end = t0 + total
    rng = np.random.default_rng(seed)
    try:
        g = bilift_phase(d, D, rng, t0 + 0.55 * total)
        if g is not None:
            return g
    except Exception:
        pass
    remaining = end - time.monotonic()
    if remaining > 1.0:
        try:
            return run(d, D, seed, remaining, PLAN + _extra_plan(), FALLBACK)
        except Exception:
            pass
    return trivial(d, D)
