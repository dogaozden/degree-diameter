"""Combined degree-6, diameter-5 search over non-abelian groups.

Two engines share one group library:
  * Haar graphs (p = 1, r = 6): batched annealing over the connection set S (cost = uncovered words).
  * Voltage lifts of K_{p,p} with r = 6/p parallel darts per pair (p = 2, 3, 6): annealing over voltages,
    cost = vertices missed by BFS (radius 5) from the 2p identity sheets.
Jobs are ordered by vertex count, so the smallest order above the record is tried first. Each job gets short
rounds, and every returned graph is checked with lib.is_valid. A valid smaller Haar graph and a tiny
always-valid graph are fallbacks.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
D_DEG = 6
LIFT_TEMP = 1.0
LIFT_PATIENCE = 2000
FALLBACK_S = [0, 179, 116, 180, 47, 306]
ORDERS = {1: (343, 351, 360, 345), 2: (172, 174, 176), 3: (115, 117, 120), 6: (58, 60)}


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given by coordinates (identity first) and a vectorised product mulfun."""
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
    """Heisenberg group mod prime p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, order q(q-1), q a prime power."""
    F = lib.GF(q)
    H = [a for a in range(1, q)]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _is_prime(x):
    return x >= 2 and all(x % q for q in range(2, int(x ** 0.5) + 1))


def group_builders(order):
    """Builders of candidate groups of exactly this order: Heisenberg/AGL types first, metacyclic next, cyclic last."""
    out = []
    for p in (2, 3, 5, 7):
        if order % (p ** 3) == 0 and _is_prime(p):
            c = order // (p ** 3)
            out.append(lambda p=p, c=c: group_heis(p) if c == 1 else group_times_cyclic(group_heis(p), c))
    for q in (5, 7, 8, 9, 11, 13):
        if order % (q * (q - 1)) == 0:
            c = order // (q * (q - 1))
            out.append(lambda q=q, c=c: group_agl(q) if c == 1 else group_times_cyclic(group_agl(q), c))
    meta = []
    for m in range(3, order):
        if order % m or order // m < 2:
            continue
        k = order // m
        lam = next((x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1), None)
        if lam is not None:
            meta.append(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
            if len(meta) >= 3:
                break
    out += meta
    out.append(lambda order=order: group_meta(order, 1, 1))
    return out


# ----------------------------------------------------------------------------- Haar search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only words involving slot i are recomputed)."""
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


def cost(MT, inv, S):
    N = MT.shape[0]
    Si = inv[S]
    P0 = MT[Si[:, None], S[None, :]].ravel()
    P1 = MT[S[:, None], Si[None, :]].ravel()
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in (P0, P1))


def haar_search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Anneal a d-subset S containing the identity (WLOG by left translation). Returns (S, cost)."""
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
        i = int(rng.integers(1, d))
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
            S = None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B) for s in S."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N).tolist()
    edges = [(a, N + b) for s in S for a, b in zip(g, MT[s].tolist())]
    return 2 * N, edges


# ----------------------------------------------------------------------------- voltage lifts

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table of the lift of K_{p,p} with r darts per pair. A-vertex i*m+x, B-vertex (p+j)*m+x."""
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
    """Vertices missed within distance 5 over the 2p identity sheets. 0 means diameter <= 5."""
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
    n = 2 * p * m
    edges = set()
    for a in range(p * m):
        for b in nb[a].tolist():
            edges.add((a, b))
    return n, sorted(edges)


def anneal_lift(MT, inv, p, r, rng, deadline):
    """Anneal voltages until cost 0 (return VOL) or the deadline (return None)."""
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
        if c <= cur or rng.random() < math.exp(-(c - cur) / LIFT_TEMP):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            VOL[i, j, t] = old
            since += 1
        if since > LIFT_PATIENCE:
            VOL, cur = fresh()
            best, since = cur, 0
    return VOL if cur == 0 else None


# ----------------------------------------------------------------------------- scheduling

def make_jobs():
    """(vertex count, p, r, group builder), ascending by vertex count; every count exceeds RECORD."""
    jobs = []
    for p, orders in ORDERS.items():
        r = D_DEG // p
        for G in orders:
            for builder in group_builders(G)[:2]:
                jobs.append((2 * p * G, p, r, builder))
    jobs.sort(key=lambda x: x[0])
    return jobs


def search_all(d, D, deadline, seed):
    rng = np.random.default_rng(seed)
    jobs = make_jobs()
    if not jobs:
        return None
    pass_slice = max(1.0, (deadline - time.monotonic()) / (2.0 * len(jobs)))
    cache, best = {}, None
    while time.monotonic() < deadline:
        attempted = 0
        for idx, (n_t, p, r, builder) in enumerate(jobs):
            now = time.monotonic()
            if now >= deadline:
                break
            if best is not None and n_t <= best[0]:
                continue
            attempted += 1
            end = min(deadline, now + pass_slice)
            try:
                if idx not in cache:
                    cache[idx] = builder()
                MT, inv = cache[idx]
                if p == 1:
                    S, c = haar_search(MT, inv, d, end, rng)
                    if S is None or c != 0:
                        continue
                    n, edges = haar_edges(MT, S)
                else:
                    VOL = anneal_lift(MT, inv, p, r, rng, end)
                    if VOL is None:
                        continue
                    n, edges = lift_graph(lift_nb(MT, inv, p, r, VOL), p, MT.shape[0])
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
            except Exception:
                continue
        if attempted == 0:
            break
    return best


# ----------------------------------------------------------------------------- small fallbacks

def safe_small(d, D):
    """Small graph that is valid for (d, D)."""
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


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(0.5, min(0.72 * time_limit, time_limit - 10.0))
    deadline = t0 + budget

    best = None
    try:
        best = search_all(d, D, deadline, seed)
    except Exception:
        best = None
    if best is not None:
        return best

    try:
        MT, inv = group_meta(33, 10, 26)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
