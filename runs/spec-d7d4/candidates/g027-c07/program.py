"""Cyclic/group-lift search for bipartite graphs of max degree d and diameter <= D.

A lift over a group Gamma with k base vertices per side is a regular bipartite graph on
2*k*|Gamma| vertices. Translation by Gamma is an automorphism, so the diameter is <= D iff
every base vertex, used as a source with group identity, reaches everything within D.
That gives 2k BFS runs per evaluation. Simulated annealing searches over layered
permutations and voltages, and the order is raised step by step. Non-cyclic groups
Z_m x| Z_k are included.

High-risk replacement: the previous legacy pipeline is dropped. The fallback is K_{d,d},
and every returned graph passes lib.is_valid.
"""
import math
import random
import time

import numpy as np

import lib


def _group_options(G):
    """All (m, k2, r) with m * k2 = G giving a semidirect product Z_m x| Z_k2 (r = 1 is cyclic)."""
    opts = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k2 = G // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def _tables(G, opt, cache):
    """Multiplication and inverse tables (identity is element 0)."""
    key = (G,) + opt
    if key not in cache:
        if len(cache) > 40:
            cache.clear()
        m, k2, r = opt
        _, mul, _ = lib.semidirect_group(m, k2, r)
        MUL = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
        INV = np.argmax(MUL == 0, axis=1).astype(np.int64)
        cache[key] = (MUL, INV)
    return cache[key]


def _dup(pi, v, k, G, d):
    """Number of repeated (target, voltage) pairs per base A-vertex (must be 0)."""
    dup = 0
    for i in range(k):
        col = pi[:, i] * G + v[:, i]
        dup += d - len(np.unique(col))
    return dup


def _nb(k, G, d, pi, pinv, v, MUL, INV):
    """Neighbour table of the lift. A-rows are i*G+x, B-rows are (k+j)*G+y."""
    xs = np.arange(G)
    nb = np.empty((2 * k * G, d), dtype=np.int64)
    for s in range(d):
        # A vertex (i, x) -> B vertex (pi[s,i], x * v[s,i])
        gm = MUL[xs[:, None], v[s][None, :]]          # (G, k)
        tgt = (k + pi[s])[None, :] * G + gm           # (G, k)
        nb[:k * G, s] = tgt.T.reshape(-1)
        # B vertex (j, y) -> A vertex (i, y * v[s,i]^-1) with i = pinv[s,j]
        ig = pinv[s]
        ginv = INV[v[s][ig]]
        gm2 = MUL[xs[:, None], ginv[None, :]]         # (G, k)
        src = ig[None, :] * G + gm2                   # (G, k)
        nb[k * G:, s] = src.T.reshape(-1)
    return nb


def _cost(nb, src, D):
    """Total number of (source, vertex) pairs not reached within D steps."""
    S = src.shape[0]
    N, d = nb.shape
    seen = np.zeros((S, N), dtype=bool)
    rows = np.arange(S)
    seen[rows, src] = True
    front = seen.copy()
    for _ in range(D):
        r, c = np.nonzero(front)
        if r.size == 0:
            break
        nxt = np.zeros((S, N), dtype=bool)
        nxt[np.repeat(r, d), nb[c].ravel()] = True
        nxt &= ~seen
        seen |= nxt
        front = nxt
    return S * N - int(seen.sum())


def _anneal(k, G, d, D, MUL, INV, deadline, rng, max_iters):
    """Anneal layered permutations and voltages. Returns (n, edges) on success, else None."""
    N = 2 * k * G
    src = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)], dtype=np.int64)
    pi = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    v = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    pinv = np.argsort(pi, axis=1)
    PEN = 4 * N

    def score(pi, pinv, v):
        dup = _dup(pi, v, k, G, d)
        nb = _nb(k, G, d, pi, pinv, v, MUL, INV)
        c = _cost(nb, src, D)
        return c + PEN * dup, nb, c, dup

    cur, nb, c, dup = score(pi, pinv, v)
    T = 0.8
    for it in range(max_iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        s = rng.randrange(d)
        if k > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            pi[s, i1], pi[s, i2] = pi[s, i2], pi[s, i1]
            pinv[s] = np.argsort(pi[s])
            undo = (1, s, i1, i2)
        else:
            i = rng.randrange(k)
            old = int(v[s, i])
            v[s, i] = rng.randrange(G)
            undo = (0, s, i, old)
        new, nnb, nc, nd = score(pi, pinv, v)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur, nb, c, dup = new, nnb, nc, nd
        else:
            if undo[0] == 1:
                _, s_, i1, i2 = undo
                pi[s_, i1], pi[s_, i2] = pi[s_, i2], pi[s_, i1]
                pinv[s_] = np.argsort(pi[s_])
            else:
                _, s_, i_, old = undo
                v[s_, i_] = old
        T = max(0.2, T * 0.9995)

    if cur == 0 and dup == 0 and c == 0:
        edges = []
        for u in range(k * G):
            for s in range(d):
                edges.append((u, int(nb[u, s])))
        return N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    deadline = start + max(1.0, min(0.85 * T, T - 5.0))
    rng = random.Random(seed)
    cache = {}
    opt_cache = {}
    KS = [1, 1, 1, 1, 2, 2, 3]
    slice_len = max(2.0, 0.12 * T)
    bump = 0

    while time.monotonic() < deadline - 0.5:
        k = rng.choice(KS)
        need = best[0] // (2 * k) + 1
        Gmax = moore // (2 * k)
        if Gmax < need:
            if k == 1:
                break
            continue
        G = min(need + bump, Gmax)
        slice_end = min(deadline, time.monotonic() + slice_len)
        found = None
        while found is None and time.monotonic() < slice_end:
            if G not in opt_cache:
                opt_cache[G] = _group_options(G)
            opt = rng.choice(opt_cache[G])
            MUL, INV = _tables(G, opt, cache)
            found = _anneal(k, G, d, D, MUL, INV, slice_end, rng, 6000)
        if found is not None:
            n, e = found
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                bump = 2 * bump + 1
                if best[0] >= moore:
                    break
                continue
        bump //= 2

    return best
