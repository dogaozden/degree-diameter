import math
import random
import time

import numpy as np

import lib

N_CAP = 6000          # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 3000          # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side


def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x k) of the Z_m lift of a k-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]. A-lift id = i*m+g,
    B-lift id = (s+j)*m+h. Every lift vertex gets exactly one neighbour per dart.
    """
    k_darts = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, k_darts), dtype=np.int64)
    for k in range(k_darts):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    The Z_m action is transitive on each fibre, so checking the base-vertex sources suffices.
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


def _anneal(s, m, dd, D, rng, deadline):
    """Simulated annealing over permutations and voltages with dd darts. Returns (P, V) or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(dd)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(dd):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(dd)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(dd), rng.randrange(s)
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
            k = rng.randrange(dd)
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


def _graph(s, m, P, V):
    """Materialise the lift as (n, edges), deduplicated. A-ids < B-ids, so edges are (a, b) with a < b."""
    dd = P.shape[0]
    Pinv = np.zeros_like(P)
    for k in range(dd):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search(s, dd, D, rng, deadline, cap):
    """For fixed s and dart count dd, find the largest m (doubling then bisection) passing annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _anneal(s, m, dd, D, rng, deadline)
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


def _fill_spare_degree(n, edges, d, rng):
    """New idea: greedily add A-B edges between non-adjacent vertices that still have spare degree.

    The graph is bipartite with A = 0..n/2-1 and B = n/2..n-1. Adding edges between A and B never
    breaks bipartiteness, never breaks the degree cap, and can only shorten distances, so a
    valid diameter-D graph stays valid. This turns a (d-1)-regular lift into a near-d-regular one.
    """
    half = n // 2
    deg = [0] * n
    es = set(edges)
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    A = [a for a in range(half) if deg[a] < d]
    B = [b for b in range(half, n) if deg[b] < d]
    out = list(edges)
    tries, limit = 0, 60 * n + 1000
    while A and B and tries < limit:
        tries += 1
        ia, ib = rng.randrange(len(A)), rng.randrange(len(B))
        a, b = A[ia], B[ib]
        if (a, b) in es:
            continue
        es.add((a, b))
        out.append((a, b))
        deg[a] += 1
        deg[b] += 1
        if deg[a] >= d:
            A[ia] = A[-1]
            A.pop()
        if deg[b] >= d:
            B[ib] = B[-1]
            B.pop()
    return out


def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges.

    Extra point-line edges (between non-incident pairs) only shorten distances, so diameter 3
    and bipartiteness are preserved while every vertex with spare degree gains neighbours.
    """
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

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # Dart counts to try: the full degree d, and d-1 (lower degree is easier to lift,
    # and the spare degree is then filled by _fill_spare_degree).
    dds = [d]
    if d - 1 >= 2:
        dds.append(d - 1)
    jobs = [(dd, s) for dd in dds for s in S_LIST]

    best = None  # (n, s, m, P, V)
    for idx, (dd, s) in enumerate(jobs):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(jobs) - idx)
        res = _search(s, dd, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4])
        e = _fill_spare_degree(n, e, d, rng)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    # Return the larger valid candidate.
    options = [c for c in (pg, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
