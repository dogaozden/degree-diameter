import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 2400          # hard cap on vertex count for all searches
ITERS = 3000          # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side for lifts


# ---------------------------------------------------------------- random bipartite search

def _nbr_table(nA, nB, h):
    """Full neighbour table: A-vertex i (id i) sees B-ids h + nA[i, k]; B-vertex j (id h + j) sees A-ids nB[j, k]."""
    return np.vstack([h + nA, nB])


def _bad(nbr, D):
    """Number of ordered vertex pairs at distance more than D. Zero iff diameter <= D (graph connected)."""
    n, d = nbr.shape
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return n * n - int(np.count_nonzero(R))


def _replace(nB, b, old, new):
    idx = int(np.nonzero(nB[b] == old)[0][0])
    nB[b, idx] = new


def _switch(nA, nB, h, d, rng):
    """Random 2-switch on a simple d-regular bipartite graph. Returns the move record, or None if rejected."""
    a1, a2 = rng.randrange(h), rng.randrange(h)
    if a1 == a2:
        return None
    k1, k2 = rng.randrange(d), rng.randrange(d)
    b1, b2 = int(nA[a1, k1]), int(nA[a2, k2])
    if b1 == b2 or (nA[a1] == b2).any() or (nA[a2] == b1).any():
        return None
    nA[a1, k1] = b2
    nA[a2, k2] = b1
    _replace(nB, b1, a1, a2)
    _replace(nB, b2, a2, a1)
    return (a1, k1, a2, k2, b1, b2)


def _undo(nA, nB, mv):
    a1, k1, a2, k2, b1, b2 = mv
    nA[a1, k1] = b1
    nA[a2, k2] = b2
    _replace(nB, b1, a2, a1)
    _replace(nB, b2, a1, a2)


def _attempt(h, d, D, rng, deadline):
    """Start from a circulant (Haar-type) d-regular bipartite graph on h+h vertices and anneal
    2-switches to kill all pairs at distance > D. Returns (nA, nB) or None."""
    nA = np.array([[(i + k) % h for k in range(d)] for i in range(h)], dtype=np.int64)
    nB = np.array([[(j - k) % h for k in range(d)] for j in range(h)], dtype=np.int64)
    cur = _bad(_nbr_table(nA, nB, h), D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = 2.0 * (1.0 - (now - t0) / span) + 0.1
        mv = _switch(nA, nB, h, d, rng)
        if mv is None:
            continue
        c = _bad(_nbr_table(nA, nB, h), D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            _undo(nA, nB, mv)
    return nA, nB


def _random_search(d, D, seed, deadline):
    """Grow the bipartite side size h by doubling/halving steps; return (h, nA, nB) for the largest success."""
    rng = random.Random(seed)
    cap_h = min(N_CAP, lib._moore_bound(d, D)) // 2
    best_h, best = d, None          # K_{d,d} is valid for D >= 2
    step = max(1, d)
    while time.monotonic() < deadline:
        h = min(best_h + step, cap_h)
        if h <= best_h:
            break
        now = time.monotonic()
        attempt_end = min(deadline, now + max(1.0, (deadline - now) / 3.0))
        res = _attempt(h, d, D, rng, attempt_end)
        if res is not None:
            best_h, best = h, (h,) + res
            step = max(1, step * 2)
        else:
            if step == 1:
                break
            step //= 2
    return best


def _edges_bipartite(nA, h, d):
    return [(i, h + int(nA[i, k])) for i in range(h) for k in range(d)]


# ---------------------------------------------------------------- Z_m lifts (fallback family)

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


# ---------------------------------------------------------------- projective / quadrangle bases

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    q = x
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return q if q >= 2 else None


def _augment(n, edges, d, seed):
    """Add point-line edges between non-incident pairs using spare degree (points 0..n/2-1, lines n/2..n-1)."""
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
            for _attempt in range(30):
                l = rng.randrange(m, n)
                if deg[l] < d and l not in adj[p]:
                    adj[p].add(l)
                    adj[l].add(p)
                    deg[p] += 1
                    deg[l] += 1
                    new_edges.append((p, l))
                    break
    return n, new_edges


def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, edges = lib.projective_plane_incidence(q)
    return _augment(n, edges, d, seed)


def _gq_incidence(q):
    """Incidence graph of the generalized quadrangle W(q): degree q+1, 2(q+1)(q^2+1) vertices, diameter 4."""
    F = lib.GF(q)
    pts_list = [v for v in itertools.product(range(q), repeat=4)
                if any(v) and next(c for c in v if c) == 1]
    pts = np.array(pts_list, dtype=np.int64)
    N = len(pts_list)
    index = {v: i for i, v in enumerate(pts_list)}
    mul, add, neg = F.mul_table, F.add_table, F._neg

    def normalize(v):
        c = next(x for x in v if x)
        s = F.inv(c)
        return tuple(F.mul(x, s) for x in v)

    covered = [set() for _ in range(N)]
    lines = []
    for i in range(N):
        a = pts_list[i]
        row = add[add[mul[a[0], pts[:, 1]], neg[mul[a[1], pts[:, 0]]]],
                  add[mul[a[2], pts[:, 3]], neg[mul[a[3], pts[:, 2]]]]]
        for j in np.nonzero(row == 0)[0].tolist():
            if j == i or j in covered[i]:
                continue
            L = {j}
            bj = pts_list[j]
            for t in range(q):
                v = tuple(F.add(a[s], F.mul(t, bj[s])) for s in range(4))
                L.add(index[normalize(v)])
            L = sorted(L)
            lines.append(L)
            for k in L:
                covered[k].update(L)
    edges = [(p, N + l) for l, L in enumerate(lines) for p in L]
    return 2 * N, edges


def _gq_augmented(d, seed):
    """W(q) incidence graph with q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, edges = _gq_incidence(q)
    return _augment(n, edges, d, seed)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.7 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    # D = 3: projective-plane based construction.
    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    # D >= 4: generalized quadrangle W(q) incidence graph, augmented with spare degree.
    gq = None
    if D >= 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            gq = cand

    if D < 2 or d < 1:
        return fallback

    # Bold alternative for D >= 4: random d-regular bipartite graphs repaired by 2-switch annealing.
    sa = None
    if D >= 4 and d >= 3:
        res = _random_search(d, D, seed, start + 0.55 * total)
        if res is not None:
            h, nA, nB = res
            n, e = 2 * h, _edges_bipartite(nA, h, d)
            if lib.is_valid(n, e, d, D):
                sa = (n, e)

    # Z_m lift search (the original family), with the remaining budget.
    deadline = start + total
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    best = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
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

    # Return the largest valid candidate.
    options = [c for c in (pg, gq, sa, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
