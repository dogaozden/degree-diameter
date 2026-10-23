"""Two-stage search for the d=6, D=5 bipartite degree-diameter case.

Stage 1 (new construction): voltage lifts of small bipartite base multigraphs. Each base has a vertices per side
and is 6-regular, built as a sum of six random permutation matrices. Its voltages live in a group G of order N,
giving 2aN vertices, and we need 2aN >= 686 to beat the record 684. Left multiplication by G is an automorphism of
the lift, so the diameter is at most D iff every one of the 2a base vertices reaches the whole lift within D steps.
That check is a handful of vectorised BFS passes. Simulated annealing on the voltages drives the number of
unreached (source, vertex) pairs to 0.

Stage 2 (inherited): Haar graphs on non-abelian groups (cost-annealed connection sets, as in the parent), which
reproduce the 684-vertex record.

Fallback: a precomputed valid 660-vertex Haar graph. Every output is checked with lib.is_valid.
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
    """Heisenberg group mod p, order p^3."""
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


def metacyclic_candidates(lo, hi, per_pair, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi. Returns tuples (N, m, k, lam)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= per_pair:
                        break
            if len(out) >= limit:
                return out
    return out


# ============================================================ stage 1: voltage lifts of small bases

def base_darts(a, d, rng):
    """Darts of a d-regular bipartite base on a+a vertices: sum of d random permutation matrices."""
    darts = []
    for _ in range(d):
        perm = rng.permutation(a)
        darts.extend((u, int(perm[u])) for u in range(a))
    return darts


def lift_arrays(MT, a, darts, volt):
    """Directed arc arrays (S, Dd) of the lift. Base vertex s has block s*N..s*N+N-1 (A: 0..a-1, B: a..2a-1).
    Dart (u, v, g) joins (A_u, x) to (B_v, x*g)."""
    N = MT.shape[0]
    xs = np.arange(N, dtype=np.int64)
    S, Dd = [], []
    for (u, v), g in zip(darts, volt):
        src = u * N + xs
        dst = (a + v) * N + MT[:, int(g)].astype(np.int64)
        S.append(src)
        S.append(dst)
        Dd.append(dst)
        Dd.append(src)
    return np.concatenate(S), np.concatenate(Dd)


def lift_cost(S, Dd, n, nb, N, D):
    """Total number of vertices not within distance D of each base-vertex identity source.
    Left multiplication by the group is an automorphism, so 0 here means diameter <= D."""
    total = 0
    for s in range(nb):
        reached = np.zeros(n, dtype=bool)
        reached[s * N] = True
        front = reached.copy()
        for _ in range(D):
            nxt = np.zeros(n, dtype=bool)
            nxt[Dd[front[S]]] = True
            nxt &= ~reached
            if not nxt.any():
                break
            reached |= nxt
            front = nxt
        total += n - int(reached.sum())
    return total


def lift_edges(MT, a, darts, volt):
    """Explicit edge list of the lift (a list, so duplicates would be visible to lib.is_valid)."""
    N = MT.shape[0]
    edges = []
    for (u, v), g in zip(darts, volt):
        col = MT[:, int(g)].tolist()
        for x in range(N):
            edges.append((u * N + x, (a + v) * N + col[x]))
    return 2 * a * N, edges


def make_cfg(a, MT, N, d, rng):
    darts = base_darts(a, d, rng)
    groups = {}
    for k, p in enumerate(darts):
        groups.setdefault(p, []).append(k)
    peers = [[j for j in groups[darts[k]] if j != k] for k in range(len(darts))]
    return {'a': a, 'N': N, 'MT': MT, 'darts': darts, 'groups': groups, 'peers': peers,
            'volt': None, 'c': None, 'since': 0}


def _fresh(cfg, rng):
    """Random voltages, distinct within each parallel class of darts."""
    volt = np.zeros(len(cfg['darts']), dtype=np.int64)
    for idx in cfg['groups'].values():
        volt[idx] = rng.choice(cfg['N'], size=len(idx), replace=False)
    return volt


def step(cfg, deadline, rng, D, temp=1.5, patience=3000):
    """Anneal the voltages of one configuration until cost 0 or the deadline; state is kept between calls."""
    N, a, darts = cfg['N'], cfg['a'], cfg['darts']
    nb = 2 * a
    n = nb * N
    nd = len(darts)

    def ev(v):
        S, Dd = lift_arrays(cfg['MT'], a, darts, v)
        return lift_cost(S, Dd, n, nb, N, D)

    if cfg['volt'] is None:
        cfg['volt'] = _fresh(cfg, rng)
        cfg['c'] = ev(cfg['volt'])
        cfg['since'] = 0
    volt, c = cfg['volt'], cfg['c']
    while c > 0 and time.monotonic() < deadline:
        if cfg['since'] > patience:
            volt = _fresh(cfg, rng)
            c = ev(volt)
            cfg['since'] = 0
            continue
        k = int(rng.integers(nd))
        forb = {int(volt[j]) for j in cfg['peers'][k]}
        if len(forb) >= N:
            cfg['since'] += 1
            continue
        nv = int(rng.integers(N))
        while nv in forb:
            nv = int(rng.integers(N))
        old = int(volt[k])
        volt[k] = nv
        c2 = ev(volt)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            cfg['since'] = 0 if c2 < c else cfg['since'] + 1
            c = c2
        else:
            volt[k] = old
            cfg['since'] += 1
    cfg['volt'], cfg['c'] = volt, c


def lift_configs(d, rng, min_n=686, width=4):
    """Configurations (base size a, group order N) with 2aN >= min_n, smallest vertex count first."""
    cfgs = []
    for a in (2, 3, 4):
        nmin = -(-min_n // (2 * a))
        for N in range(nmin, nmin + width):
            specs = [(N, 1, 1)]  # cyclic group
            specs += [(m, k, lam) for (_, m, k, lam) in metacyclic_candidates(N, N, 2, 2)]
            for (m, k, lam) in specs:
                try:
                    MT, _ = group_meta(m, k, lam)
                except Exception:
                    continue
                cfgs.append(make_cfg(a, MT, N, d, rng))
    cfgs.sort(key=lambda c: (2 * c['a'] * c['N'], c['a']))
    return cfgs


def lift_stage(cfgs, d, D, rng, deadline):
    """Round-robin annealing over configurations with growing slices. Returns (n, edges) with n > 684 or None."""
    slice_len = 0.3
    while time.monotonic() < deadline - 0.05:
        active = [c for c in cfgs if not c.get('done')]
        if not active:
            break
        for cfg in active:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_len)
            try:
                step(cfg, end, rng, D)
            except Exception:
                cfg['done'] = True
                continue
            if cfg['c'] == 0:
                n, edges = lift_edges(cfg['MT'], cfg['a'], cfg['darts'], cfg['volt'])
                if n > 684 and lib.is_valid(n, edges, d, D):
                    return n, edges
                cfg['done'] = True
        slice_len = min(slice_len * 1.5, 5.0)
    return None


# ============================================================ stage 2: Haar graphs (inherited)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    P1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
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
    """Annealing over d-subsets of the group, with restarts. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
            cur = None
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
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
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
    """Time-sliced round-robin over Haar candidate groups; returns a valid graph."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    cache = {}
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (name, builder) in enumerate(plan):
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = builder()
                except Exception:
                    cache[idx] = None
            if cache[idx] is None:
                continue
            MT, inv = cache[idx]
            end = min(deadline, now + slice_len)
            try:
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
        slice_len = min(slice_len * 1.5, 6.0)
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]
for _N, _m, _k, _lam in metacyclic_candidates(343, 372, 2, 28):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))
for _N, _m, _k, _lam in metacyclic_candidates(342, 342, 2, 4):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


# ============================================================ entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.85 * time_limit
    rng = np.random.default_rng(seed)
    try:
        cfgs = lift_configs(d, rng, min_n=686)
        res = lift_stage(cfgs, d, D, rng, t0 + 0.55 * budget)
        if res is not None:
            return res
    except Exception:
        pass
    remaining = max(1.0, t0 + budget - time.monotonic())
    return run(d, D, seed, remaining / 0.8, PLAN, FALLBACK)
