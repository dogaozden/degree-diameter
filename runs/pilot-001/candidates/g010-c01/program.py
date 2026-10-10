import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                    # hard cap on vertex count
ITERS = 3000                    # annealing iterations per attempt
S_LIST = (1, 2, 3, 4)           # base vertices per side
A_LIST = (1, 2, 3, 4)           # group shapes Z_a x Z_b with b growing (a = 1 is cyclic)


def _tables(a, b):
    """Addition and negation tables of the abelian group Z_a x Z_b, element x = hi*b + lo."""
    m = a * b
    X = np.arange(m, dtype=np.int64)
    hi, lo = X // b, X % b
    add = (((hi[:, None] + hi[None, :]) % a) * b + (lo[:, None] + lo[None, :]) % b).astype(np.int64)
    neg = (((-hi) % a) * b + (-lo) % b).astype(np.int64)
    return add, neg


def _neighbors(P, Pinv, V, s, m, add, neg):
    """Neighbour table (2*s*m x d) of the G-lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex (i, g) to B-vertex (P[k,i], g+V[k,i]).
    A-lift id = i*m + g, B-lift id = (s+j)*m + h.
    """
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + add[g, int(V[k, i])]
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + add[g, neg[int(V[k, i])]]
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    Translations by G act transitively on each fibre, so base-vertex sources suffice.
    """
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


def _anneal(s, m, d, D, rng, deadline, add, neg):
    """Simulated annealing over base permutations and group voltages. Returns (P, V) or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m, add, neg)
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
            cand = _neighbors(P, Pinv, V, s, m, add, neg)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m, add, neg)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d, add, neg):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m, add, neg)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, a, d, D, rng, deadline, cap):
    """For fixed s and group shape Z_a x Z_b, find the largest b (doubling then bisection)."""
    best = None
    lo, hi = 0, None
    b = 1
    while time.monotonic() < deadline:
        m = a * b
        if 2 * s * m > cap:
            hi = b
        else:
            add, neg = _tables(a, b)
            st = _anneal(s, m, d, D, rng, deadline, add, neg)
            if st is not None:
                lo = b
                best = (m, st[0], st[1], add, neg)
            else:
                hi = b
        if hi is None:
            b = 2 * lo
        else:
            if hi - lo <= 1:
                break
            b = (lo + hi) // 2
        if b < 1:
            break
    return best


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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.6 * time_limit - 1.0)

    # Safe fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    # D = 3: projective-plane construction (exact when d-1 is a prime power).
    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    if D < 2 or d < 1:
        return fallback

    # Bold change: search lifts over abelian groups Z_a x Z_b (not only cyclic),
    # across several base sizes, so orders can take many more values.
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    combos = [(s, a) for s in S_LIST for a in A_LIST]
    best = None  # (n, s, m, P, V, add, neg)
    for idx, (s, a) in enumerate(combos):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(combos) - idx)
        res = _search(s, a, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V, add, neg = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V, add, neg)

    lift = None
    if best is not None:
        n, s, m, P, V, add, neg = best
        n2, e = _graph(s, m, P, V, d, add, neg)
        if lib.is_valid(n2, e, d, D):
            lift = (n2, e)

    options = [c for c in (pg, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
