"""Degree-6, diameter-5 search that combines two approaches.

1. Haar graphs (p = 1 lifts) over non-abelian groups of order G >= 343. The graph has 2G vertices. Annealing
   on the connection set S uses the exact word-cover cost: the diameter is at most 5 iff
   (S^-1 S)^2 = G and (S S^-1)^2 = G.
2. Voltage lifts of small bipartite base graphs K_{p,p} with p*r = 6 (p = 2, r = 3 and p = 3, r = 2). The lift
   has 2*p*G vertices. Cost is the number of vertices missed by BFS (depth 5) from the 2p identity sheets.

Jobs are sorted by vertex count and run in order, with equal time shares. Each job is annealed, and any
result is checked with lib.is_valid before it is kept. The largest valid graph wins. If nothing beats the
Haar fallback of order 660, that fallback is returned. Non-target cases get a small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
FALLBACK_G = (33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]
TEMP_HAAR = 0.45
PATIENCE_HAAR = 4000
TEMP_LIFT = 1.0
PATIENCE_LIFT = 2000


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
    """Table of a group given by an (N, c) coordinate array (row 0 = identity) and a vectorised product."""
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


def group_agl(q):
    """AGL(1, q) for a prime power q: maps t -> a*t + b, with product (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
    F = lib.GF(q)
    H = [a for a in range(1, q)]
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def make_group(spec):
    """Build (MT, inv) for a group spec."""
    tag = spec[0]
    if tag == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    if tag == 'cyc':
        return group_meta(spec[1], 1, 1)
    if tag == 'heis':
        return group_heis(spec[1])
    if tag == 'heis_z':
        return group_times_cyclic(group_heis(spec[1]), spec[2])
    if tag == 'agl_z':
        return group_times_cyclic(group_agl(spec[1]), spec[2])
    raise ValueError(f"unknown group spec {spec}")


def meta_specs(G, limit=2):
    """Up to `limit` non-abelian metacyclic groups Z_m x| Z_k of order G, one lam per m."""
    out = []
    for m in range(3, G):
        if G % m:
            continue
        k = G // m
        if k < 2:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                out.append(('meta', m, k, lam))
                break
        if len(out) >= limit:
            break
    return out


# ----------------------------------------------------------------------------- Haar search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(S_i^-1 S_j, S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements on both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


def search(MT, inv, d, deadline, rng, K=24, temp=TEMP_HAAR, patience=PATIENCE_HAAR):
    """Simulated annealing with restarts over d-subsets containing 0 (WLOG by left translation).
    Returns (best S, best cost)."""
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
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, with (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ----------------------------------------------------------------------------- voltage lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table. A-vertex i*m+x, B-vertex (p+j)*m+x. Dart (i,j,t) with voltage g joins (i,x) to (j, x*g)."""
    m = MT.shape[0]
    nb = np.empty((2 * p * m, p * r), dtype=np.int64)
    for i in range(p):
        cols = [(p + j) * m + MT[:, VOL[i, j, t]] for j in range(p) for t in range(r)]
        nb[i * m:(i + 1) * m] = np.stack(cols, axis=1)
    for j in range(p):
        cols = [i * m + MT[:, inv[VOL[i, j, t]]] for i in range(p) for t in range(r)]
        nb[(p + j) * m:(p + j + 1) * m] = np.stack(cols, axis=1)
    return nb


def lift_cost(nb, m, p):
    """Vertices missed within distance 5 from the 2p identity sheets (0 = diameter <= 5)."""
    n = nb.shape[0]
    total = 0
    for u in range(2 * p):
        src = u * m
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(5):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def lift_graph(nb, p, m):
    """Edge list of the lift, read from the A-side rows."""
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return 2 * p * m, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages until cost 0 (returns VOL) or the deadline (returns None)."""
    m = MT.shape[0]

    def fresh():
        VOL = rng.integers(0, m, size=(p, p, r))
        return VOL, lift_cost(lift_nb(MT, inv, p, r, VOL), m, p)

    VOL, cur = fresh()
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        i, j, t = int(rng.integers(p)), int(rng.integers(p)), int(rng.integers(r))
        old = int(VOL[i, j, t])
        new = int(rng.integers(m))
        if new == old:
            continue
        VOL[i, j, t] = new
        c = lift_cost(lift_nb(MT, inv, p, r, VOL), m, p)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP_LIFT):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            VOL[i, j, t] = old
            since += 1
        if since > PATIENCE_LIFT:
            VOL, cur = fresh()
            best, since = cur, 0
    return VOL if cur == 0 else None


# ----------------------------------------------------------------------------- jobs and fallbacks

def make_jobs():
    """Jobs (vertex count, kind, p, r, group spec), sorted by vertex count so the smallest sizes above 684 come first."""
    haar = [(343, ('heis', 7)), (351, ('heis_z', 3, 13)), (360, ('agl_z', 9, 5)), (360, ('agl_z', 5, 18))]
    for G in (344, 348, 352, 356):
        haar += [(G, s) for s in meta_specs(G, 1)]
    jobs = [(2 * G, 'haar', 1, 6, spec) for G, spec in haar]
    for p, r, Gs in ((2, 3, (172, 173, 174)), (3, 2, (115, 116))):
        for G in Gs:
            for spec in [('cyc', G)] + meta_specs(G, 1):
                jobs.append((2 * p * G, 'lift', p, r, spec))
    jobs.sort(key=lambda j: j[0])
    return jobs


def run_job(job, rng, deadline, d, D):
    """Run one job until its deadline. Returns a checked (n, edges) or None."""
    _, kind, p, r, spec = job
    MT, inv = make_group(spec)
    if kind == 'haar':
        S, c = search(MT, inv, d, deadline, rng)
        if S is None or c != 0:
            return None
        n, edges = haar_edges(MT, S)
    else:
        VOL = anneal_lift(MT, inv, p, r, rng, deadline)
        if VOL is None:
            return None
        n, edges = lift_graph(lift_nb(MT, inv, p, r, VOL), p, MT.shape[0])
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def safe_small(d, D):
    """Small always-valid graph for any (d, D). Covers the d=3, D=3 calibration (PG(2,2), 14 vertices)."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        try:
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 1, []


def fallback_graph(d, D):
    """Valid Haar graph of order 660 (Z_33 x| Z_10), used when no job beats it."""
    try:
        MT, inv = group_meta(*FALLBACK_G)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.72 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    jobs = make_jobs()
    for idx, job in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        if best is not None and job[0] <= best[0]:
            continue
        share = (deadline - now) / (len(jobs) - idx)
        try:
            res = run_job(job, rng, now + share, d, D)
        except Exception:
            res = None
        if res is not None:
            best = res

    if best is not None:
        return best
    return fallback_graph(d, D)
