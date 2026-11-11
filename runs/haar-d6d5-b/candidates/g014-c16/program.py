"""Voltage lifts over 2k-vertex bipartite base graphs (k = 2, 3, 4) for the bipartite degree-diameter problem.

Construction: a base graph with k A-vertices and k B-vertices, 6 layers, each layer a random perfect matching
between A and B. Each dart carries a voltage in a finite group G. The lift has 2kN vertices (N = |G|), is
6-regular, and is bipartite. Left multiplication by h is an automorphism, so the diameter is at most 5 iff
every base vertex's identity copy reaches all vertices within 5 steps. The cost is the number of unreached
(source, vertex) pairs and is computed with one boolean matrix product per BFS step.

Search: simulated annealing on the voltages, one slice per (k, group) configuration, round-robin over
configurations ordered by lift size. Only lifts larger than the current best are searched. Every returned
graph is checked with lib.is_valid. The fallback is a checked Haar graph of order 660, or a trivial graph.
"""
import itertools
import math
import time

import numpy as np

import lib

D_TARGET = 5
SLICE = 1.2
RECORD = 684


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, index a*k + j, identity index 0."""
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


SPECIAL = {
    'sl2_5': (lambda: group_sl2(5), 120),
    'sl2_5x2': (lambda: group_times_cyclic(group_sl2(5), 2), 240),
    'sl2_5x3': (lambda: group_times_cyclic(group_sl2(5), 3), 360),
    'sl2_7': (lambda: group_sl2(7), 336),
    'agl11': (lambda: group_agl(11), 110),
    'agl13': (lambda: group_agl(13), 156),
    'agl16': (lambda: group_agl(16), 240),
    'agl17': (lambda: group_agl(17), 272),
    'agl19': (lambda: group_agl(19), 342),
    'heis5': (lambda: group_heis(5), 125),
    'heis5x2': (lambda: group_times_cyclic(group_heis(5), 2), 250),
    'heis5x3': (lambda: group_times_cyclic(group_heis(5), 3), 375),
    'heis7': (lambda: group_heis(7), 343),
}


def get_group(key):
    if key[0] == 'm':
        return group_meta(key[1], key[2], key[3])
    return SPECIAL[key[1]][0]()


# ------------------------------------------------------------------------- lift model

def lift_model(MT, inv, k, sig):
    """Lift of the base graph (k A-vertices, k B-vertices, layer l matches A_i to B_{sig[l,i]}).
    A-vertex (i,x) has id i*N + x; B-vertex (j,y) has id k*N + j*N + y.
    Returns (n, adj_of, cost) where cost(v) counts pairs (source, vertex) not within distance 5."""
    N = MT.shape[0]
    n = 2 * k * N
    MTc = np.ascontiguousarray(MT.T)           # MTc[g][x] = x*g
    sig_inv = np.argsort(sig, axis=1)
    sources = np.array([i * N for i in range(k)] + [k * N + j * N for j in range(k)], dtype=np.int64)
    S = len(sources)
    cols = np.arange(S)

    def adj_of(v):
        adj = np.empty((n, 6), dtype=np.int64)
        for i in range(k):
            for l in range(6):
                j = int(sig[l, i])
                g = int(v[l, i])
                adj[i * N:(i + 1) * N, l] = k * N + j * N + MTc[g]
        for j in range(k):
            for l in range(6):
                i = int(sig_inv[l, j])
                g = int(v[l, i])
                adj[k * N + j * N:k * N + (j + 1) * N, l] = i * N + MTc[int(inv[g])]
        return adj

    def cost(v):
        adj = adj_of(v)
        R = np.zeros((n, S), dtype=bool)
        R[sources, cols] = True
        for _ in range(D_TARGET):
            R = R | R[adj].any(axis=1)
        return n * S - int(R.sum())

    return n, adj_of, cost


def edges_of(adj, k, N):
    E = set()
    for r in range(k * N):
        for b in adj[r]:
            E.add((r, int(b)))
    return sorted(E)


def anneal(cost, N, k, rng, t_end):
    v = rng.integers(0, N, size=(6, k))
    cur = cost(v)
    best, bestv = cur, v.copy()
    T, stall = 1.5, 0
    while cur > 0 and time.monotonic() < t_end:
        l = int(rng.integers(6))
        i = int(rng.integers(k))
        old = int(v[l, i])
        v[l, i] = int(rng.integers(N))
        c = cost(v)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if cur < best:
                best, bestv, stall = cur, v.copy(), 0
        else:
            v[l, i] = old
        stall += 1
        T = max(0.5, T * 0.999)
        if stall > 3000:
            v = rng.integers(0, N, size=(6, k))
            cur = cost(v)
            T, stall = 1.5, 0
            if cur < best:
                best, bestv = cur, v.copy()
    return best, bestv


def search_lift(MT, inv, k, rng, t_end):
    N = MT.shape[0]
    sig = np.array([rng.permutation(k) for _ in range(6)], dtype=np.int64)
    n, adj_of, cost = lift_model(MT, inv, k, sig)
    c, v = anneal(cost, N, k, rng, t_end)
    if c != 0:
        return None
    return n, edges_of(adj_of(v), k, N)


# ------------------------------------------------------------------------ fallbacks

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


# ------------------------------------------------------------------------- planning

def make_entries():
    HI = min(lib.moore_bound(6, D_TARGET), 1556)
    specs = []
    for N in range(80, 400):
        found = 0
        for k2 in range(2, N):
            if N % k2:
                continue
            m = N // k2
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k2, m) == 1:
                    specs.append((N, ('m', m, k2, lam)))
                    found += 1
                    break
            if found >= 2:
                break
    for name, (_, N) in SPECIAL.items():
        specs.append((N, ('s', name)))
    entries = []
    for N, key in specs:
        for k in (2, 3, 4):
            n = 2 * k * N
            if RECORD < n <= HI:
                entries.append((n, k, key))
    entries.sort(key=lambda e: (e[0], e[1]))
    return entries[:40]


def build(d, D, seed, time_limit):
    if (d, D) != (6, 5):
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(2.0, 0.8 * time_limit - 1.5)
    rng = np.random.default_rng(seed)
    HI = min(lib.moore_bound(6, D_TARGET), 1556)

    best = None
    try:
        MT, _ = group_meta(33, 10, 26)
        best = checked(MT, [0, 179, 116, 180, 47, 306], 6, 5)
    except Exception:
        best = None
    if best is None:
        best = trivial(6, 5)
    best_n = best[0]

    entries = make_entries()
    cache = {}
    while time.monotonic() < deadline:
        progressed = False
        for n_e, k, key in entries:
            if time.monotonic() >= deadline:
                break
            if n_e <= best_n:
                continue
            if key not in cache:
                try:
                    cache[key] = get_group(key)
                except Exception:
                    cache[key] = None
            if cache[key] is None:
                continue
            MT, inv = cache[key]
            N = MT.shape[0]
            n = 2 * k * N
            if n <= best_n or n > HI:
                continue
            progressed = True
            t_end = min(deadline, time.monotonic() + SLICE)
            try:
                res = search_lift(MT, inv, k, rng, t_end)
            except Exception:
                res = None
            if res is not None:
                nn, edges = res
                if nn > best_n and lib.is_valid(nn, edges, 6, 5):
                    best = (nn, edges)
                    best_n = nn
        if not progressed:
            break
    return best
