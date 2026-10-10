import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per lift attempt
ITERS_SW = 4000               # switch-annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side


# ---------------------------------------------------------------- Z_m lifts (baseline)

def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (by doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _anneal(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ------------------------------------------------------- projective-plane based (D = 3)

def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    rng = random.Random(seed)
    new_edges = list(edges)
    for _ in range(3):
        pts = [p for p in range(m) if deg[p] < d]
        rng.shuffle(pts)
        for p in pts:
            if deg[p] >= d:
                continue
            cands = [l for l in range(m, n) if deg[l] < d and l not in adj[p]]
            if not cands:
                continue
            l = rng.choice(cands)
            adj[p].add(l)
            adj[l].add(p)
            deg[p] += 1
            deg[l] += 1
            new_edges.append((p, l))
    return n, new_edges


# ------------------------------------------- NEW: switch-based search on regular bipartite graphs

def _reach_bad(nb, n, D):
    """NEW helper: number of ordered vertex pairs (u != v) at distance > D.

    nb is the n x d neighbour table of a simple graph. Reach sets are kept as rows of a
    boolean matrix and grown one step at a time, so the whole graph is evaluated at once.
    """
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        M = R.copy()
        for k in range(nb.shape[1]):
            M |= R[nb[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return n * n - int(np.count_nonzero(R))


def _do_switch(nb, a1, k1, a2, k2):
    """NEW: exchange the B-endpoints of edges (a1, nb[a1,k1]) and (a2, nb[a2,k2]).

    Applying the same call twice restores the graph, so it doubles as its own undo.
    """
    b1 = int(nb[a1, k1])
    b2 = int(nb[a2, k2])
    s1 = int(np.flatnonzero(nb[b1] == a1)[0])
    s2 = int(np.flatnonzero(nb[b2] == a2)[0])
    nb[a1, k1] = b2
    nb[a2, k2] = b1
    nb[b1, s1] = a2
    nb[b2, s2] = a1


def _switch_anneal(h, d, D, rng, deadline):
    """NEW: anneal a simple d-regular bipartite graph on h+h vertices, minimising bad pairs.

    Starts from a circulant (Haar-type) graph with d distinct shifts and only applies
    degree-preserving edge switches, so regularity and simplicity hold throughout.
    Returns the neighbour table of a graph of diameter <= D, or None.
    """
    n = 2 * h
    shifts = rng.sample(range(h), d)
    nb = np.empty((n, d), dtype=np.int64)
    for k, s in enumerate(shifts):
        for i in range(h):
            nb[i, k] = h + (i + s) % h
            nb[h + i, k] = (i - s) % h
    cur = _reach_bad(nb, n, D)
    for it in range(ITERS_SW):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / ITERS_SW) + 0.05
        a1, a2 = rng.randrange(h), rng.randrange(h)
        if a1 == a2:
            continue
        k1, k2 = rng.randrange(d), rng.randrange(d)
        b1, b2 = int(nb[a1, k1]), int(nb[a2, k2])
        if (nb[a1] == b2).any() or (nb[a2] == b1).any():
            continue
        _do_switch(nb, a1, k1, a2, k2)
        c = _reach_bad(nb, n, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            _do_switch(nb, a1, k1, a2, k2)
    return nb if cur == 0 else None


def _switch_search(d, D, seed, deadline, h, hcap):
    """NEW: bracket and bisect the half-size h for which switch annealing succeeds."""
    rng = random.Random(seed * 31 + 17)
    best = None
    lo, hi = None, None
    while time.monotonic() < deadline:
        h = max(d, min(h, hcap))
        if lo is not None and hi is not None and hi - lo <= 1:
            break
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(0.5, remaining * 0.45))
        nb = _switch_anneal(h, d, D, rng, slice_end)
        if nb is not None:
            lo = h
            best = (h, nb)
            if hi is None:
                if lo >= hcap:
                    break
                h = min(hcap, max(h + 1, 2 * h))
            else:
                h = (lo + hi) // 2
        else:
            hi = h
            if lo is None:
                if h <= d:
                    break
                h = max(d, (h * 2) // 3)
            else:
                h = (lo + hi) // 2
    return best


# ------------------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 1.0)
    end = start + total
    base_deadline = start + 0.35 * total

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    # D = 3: projective-plane construction, exact when d-1 is a prime power.
    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # Baseline: Z_m lifts of small bipartite bases.
    best = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= base_deadline:
            break
        slice_end = now + (base_deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    options = [c for c in (pg, lift, fallback) if c is not None]
    result = max(options, key=lambda c: c[0])

    # NEW: switch-based search on d-regular bipartite graphs, aiming to beat the baseline.
    if d >= 3 and result[0] < cap and time.monotonic() < end:
        hcap = cap // 2
        h0 = result[0] // 2 + 1
        sw = _switch_search(d, D, seed, end, h0, hcap)
        if sw is not None:
            h, nb = sw
            edges = [(i, int(nb[i, k])) for i in range(h) for k in range(d)]
            n = 2 * h
            if n > result[0] and lib.is_valid(n, edges, d, D):
                result = (n, edges)

    return result
