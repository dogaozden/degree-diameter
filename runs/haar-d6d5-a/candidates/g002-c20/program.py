"""Combined degree-6, diameter-5 search.

Two families are searched and the largest valid graph wins:
  1. Haar graphs (base = 2 vertices, 6 darts) over non-abelian groups of order > 342. Connection set S of size 6
     is annealed with the exact coverage cost: the graph has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
  2. Voltage lifts of K_{p,p} with r parallel darts (p*r = 6, p in {6, 3, 2}) over groups of order > 684/(2p),
     annealed by BFS from the 2p identity sheets.

Every returned graph is checked with lib.is_valid. Fallbacks: a valid smaller Haar graph, then a tiny graph.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
LIFT_TEMP = 1.0
LIFT_PATIENCE = 2000
HAAR_TEMP = 0.45
HAAR_PATIENCE = 4000
HAAR_K = 24

FALLBACK_SPEC = (33, 10, 26)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ------------------------------------------------------------------------------ group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given by an (N, c) coordinate array (identity first) and a vectorised product."""
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


def group_agl(q):
    """AGL(1, q) for a prime power q: maps t -> a t + b, order q(q-1)."""
    F = lib.GF(q)
    H = [a for a in range(1, q) if F.pow(a, q - 1) == 1]
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


def group_cyclic(N):
    a = np.arange(N, dtype=np.int64)
    return _finish((a[:, None] + a[None, :]) % N)


def make_group(spec):
    kind = spec[0]
    if kind == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    if kind == 'heis':
        return group_heis(spec[1])
    if kind == 'heis_cyc':
        return group_times_cyclic(group_heis(spec[1]), spec[2])
    if kind == 'agl_cyc':
        return group_times_cyclic(group_agl(spec[1]), spec[2])
    if kind == 'cyc':
        return group_cyclic(spec[1])
    raise ValueError(kind)


def specs_of_order(G):
    """Candidate groups of order G: some metacyclic non-abelian ones, Heisenberg if applicable, then cyclic."""
    specs = []
    for k in range(2, G):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                specs.append(('meta', m, k, lam))
    picked = specs[::max(1, len(specs) // 3)][:4]
    p = round(G ** (1.0 / 3.0))
    if p >= 2 and p ** 3 == G and lib.is_prime_power(p):
        picked.append(('heis', p))
    picked.append(('cyc', G))
    return picked


# ------------------------------------------------------------------ Haar graph search (p = 1)

def _pairs_cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements on both sides (0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    p0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    p1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return sum(N - int(_pairs_cover(MT, N, P).sum()) for P in (p0, p1))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only slot-i words recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _pairs_cover(MT, N, F)
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


def search_haar(MT, inv, d, deadline, rng):
    """Anneal a d-subset S of the group (0 included WLOG) until cost 0 or the deadline."""
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
        X = rng.integers(0, N, size=HAAR_K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / HAAR_TEMP):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
        since += 1
        if since > HAAR_PATIENCE:
            S = None
    return best, bestc


def haar_edges(MT, S):
    """A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# ------------------------------------------------------------- voltage lifts (p > 1)

def lift_nb(MT, inv, p, r, VOL):
    """Neighbour table of the lift of K_{p,p} with r parallel darts per pair. A-vertex i*m+x, B-vertex (p+j)*m+x."""
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
    """Vertices missed within distance 5 over the 2p identity sheets (0 = diameter <= 5)."""
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


# ------------------------------------------------------------------------- fallbacks

def safe_small(d, D):
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


# ------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 10.0))
    end = t0 + budget
    rng = np.random.default_rng(seed)
    best = None

    def consider(g):
        nonlocal best
        if g is not None and (best is None or g[0] > best[0]):
            best = g

    # Stage 1: Haar graphs (p = 1, 6 darts) over non-abelian groups of order > 342.
    haar_specs = [('heis_cyc', 3, 13), ('heis', 7), ('agl_cyc', 9, 5), ('agl_cyc', 5, 18)]
    haar_end = t0 + 0.6 * budget
    haar_cache = {}
    for idx, spec in enumerate(haar_specs):
        now = time.monotonic()
        if now >= haar_end:
            break
        share = (haar_end - now) / (len(haar_specs) - idx)
        try:
            if spec not in haar_cache:
                haar_cache[spec] = make_group(spec)
            MT, inv = haar_cache[spec]
            S, c = search_haar(MT, inv, d, now + share, rng)
            if S is not None and c == 0:
                consider(checked_haar(MT, S, d, D))
        except Exception:
            continue

    # Stage 2: voltage lifts of K_{p,p} with r darts per pair (p * r = 6, p > 1), sorted by vertex count.
    jobs = []
    for p, r in ((6, 1), (3, 2), (2, 3)):
        g_lo = RECORD // (2 * p) + 1
        for G in range(g_lo, g_lo + 3):
            for spec in specs_of_order(G):
                jobs.append((2 * p * G, p, r, spec))
    jobs.sort(key=lambda x: x[0])

    lift_cache = {}
    for idx, (n_t, p, r, spec) in enumerate(jobs):
        now = time.monotonic()
        if now >= end:
            break
        if best is not None and n_t <= best[0]:
            continue
        share = (end - now) / max(1, min(len(jobs) - idx, 12))
        try:
            if spec not in lift_cache:
                lift_cache[spec] = make_group(spec)
            MT, inv = lift_cache[spec]
            VOL = anneal_lift(MT, inv, p, r, rng, now + share)
            if VOL is None:
                continue
            nb = lift_nb(MT, inv, p, r, VOL)
            n, edges = lift_graph(nb, p, MT.shape[0])
            if lib.is_valid(n, edges, d, D):
                consider((n, edges))
        except Exception:
            continue

    if best is not None:
        return best

    try:
        MT, inv = group_meta(*FALLBACK_SPEC)
        g = checked_haar(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return safe_small(d, D)
