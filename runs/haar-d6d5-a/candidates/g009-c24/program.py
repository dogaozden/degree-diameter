"""Lift-search plus Haar fallback for the bipartite degree-diameter problem (d=6, D=5).

STAGE 1 (new construction): a 4-vertex base multigraph with parts A={0,1} and B={2,3}. Each base
vertex has degree 6, and parallel darts between a pair carry distinct voltages. Each dart (u, v, g)
joins (u, x) to (v, x*g) for every x in a metacyclic group G of order N, so the lift has 4N vertices
and is 6-regular and bipartite. Left multiplication by any h in G is an automorphism, so the diameter
is at most 5 iff every fibre representative (u, e), u in {0,1,2,3}, reaches all vertices within 5 steps.
Voltages are annealed to minimise the number of unreached vertices. A valid lift has order 4N >= 688,
which beats the record 684.

STAGE 2 (parent): Haar-graph search over groups of order 342..360, with the same safe fallback.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
BASE_N = 4
PATTERNS = [
    [(0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3)],
    [(0, 2, 4), (0, 3, 2), (1, 2, 2), (1, 3, 4)],
    [(0, 2, 2), (0, 3, 4), (1, 2, 4), (1, 3, 2)],
]


# ----------------------------------------------------------------------------- group tables

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
    """Table of a group given by an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, per_order=2, limit=12):
    """Non-abelian Z_m x|_lam Z_k groups of order N in [lo, hi], smallest order first."""
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
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                out.append((N, m, k, lam))
                found += 1
                if found >= per_order:
                    break
    return out[:limit]


# ------------------------------------------------------------- stage 1: voltage lifts (new)

def lift_arrays(MT, N, darts, volts):
    """Edge endpoint arrays (eu, ev) of the lift: dart k = (u, v) with voltage volts[k] joins u*N+x to v*N+x*g."""
    x = np.arange(N, dtype=np.int64)
    eu = np.concatenate([u * N + x for (u, _) in darts])
    ev = np.concatenate([v * N + MT[x, int(g)].astype(np.int64) for (_, v), g in zip(darts, volts)])
    return eu, ev


def lift_nb(n, eu, ev):
    """n x DEG neighbour array of the lift (every vertex has degree DEG by construction)."""
    src = np.concatenate([eu, ev])
    dst = np.concatenate([ev, eu])
    order = np.argsort(src, kind="stable")
    return dst[order].reshape(n, DEG)


def lift_cost(nb, sources):
    """Total number of vertices NOT within DIAM steps of the given source vertices. 0 means valid."""
    n = nb.shape[0]
    total = 0
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(DIAM):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def anneal_lift(MT, N, pattern, deadline, rng):
    """Anneal voltages for a base pattern over the group. Returns a voltage vector with cost 0, or None."""
    darts = [(u, v) for u, v, mult in pattern for _ in range(mult)]
    K = len(darts)
    n = BASE_N * N
    sources = [u * N for u in range(BASE_N)]
    slots = {}
    for k, pr in enumerate(darts):
        slots.setdefault(pr, []).append(k)

    def fresh():
        vol = np.zeros(K, dtype=np.int64)
        for idx in slots.values():
            vol[idx] = rng.choice(N, size=len(idx), replace=False)
        return vol

    def score(vol):
        eu, ev = lift_arrays(MT, N, darts, vol)
        return lift_cost(lift_nb(n, eu, ev), sources)

    def clash(vol, k, g):
        return any(vol[j] == g for j in slots[darts[k]] if j != k)

    vol = fresh()
    cur = score(vol)
    since = 0
    T = 0.5
    while cur > 0 and time.monotonic() < deadline:
        if since > 3000:
            vol = fresh()
            cur = score(vol)
            since = 0
            continue
        k = int(rng.integers(K))
        g = int(rng.integers(N))
        if g == vol[k] or clash(vol, k, g):
            since += 1
            continue
        old = vol[k]
        vol[k] = g
        c = score(vol)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            if c < cur:
                since = 0
            cur = c
        else:
            vol[k] = old
        since += 1
    if cur == 0:
        return vol
    return None


def lift_stage(d, D, deadline, rng):
    """Search metacyclic groups of order 172..200 (4N >= 688 > 684). Returns the largest valid (n, edges) or None."""
    groups = metacyclic_candidates(172, 200, per_order=2, limit=14)
    best = None
    for idx, (N, m, k, lam) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(groups) - idx)
        try:
            MT, _ = group_meta(m, k, lam)
            pattern = PATTERNS[idx % len(PATTERNS)]
            vol = anneal_lift(MT, N, pattern, slice_end, rng)
            if vol is None:
                continue
            darts = [(u, v) for u, v, mult in pattern for _ in range(mult)]
            eu, ev = lift_arrays(MT, N, darts, vol)
            edges = [(int(a), int(b)) for a, b in zip(eu, ev)]
            n = BASE_N * N
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    return best


# ------------------------------------------------------------------ stage 2: Haar search (parent)

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
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
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


def build_plan():
    plan = []
    for N, m, k, lam in metacyclic_candidates(342, 360):
        plan.append((f'Z{m} x| Z{k} lam={lam}, order {N}',
                     (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1))
    plan.append(('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 2))
    return plan


PLAN = build_plan()
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ------------------------------------------------------------------------------------ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    try:
        found = lift_stage(d, D, t0 + 0.45 * time_limit, rng)
    except Exception:
        found = None
    if found is not None:
        return found
    tl = (end_all - time.monotonic()) / 0.80
    if tl > 0.5:
        return run(d, D, seed, tl, PLAN, FALLBACK)
    return trivial(d, D)
