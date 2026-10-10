import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GMAX = 1200                   # largest group order considered for voltage lifts
K_MAX = 6                     # largest k in the semidirect groups Z_m x| Z_k


def _group_tables(key):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a, b) coded as a*k+b.

    key = (m, k, r) with r^k = 1 mod m and gcd(r, m) = 1. The cyclic group Z_G is (G, 1, 1).
    Returns (G, T, inv) with T[x, y] = x*y and inv[x] = x^{-1}; identity is index 0.
    """
    m, k, r = key
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, e, m) for e in range(k)], dtype=np.int64)
    # (a, b) * (c, d) = (a + r^b c, b + d)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    # (a, b)^{-1} = (-r^{-b} a, -b)
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return G, T, inv


def _neighbors(P, Pinv, V, s, G, T, inv):
    """Neighbour table (2sG x d) of the group lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex (i, x) to B-vertex (P[k, i], x*g) with g = V[k, i].
    Equivalently B-vertex (j, y) joins A-vertex (Pinv[k, j], y*g^{-1}).
    A-lift id = i*G + x, B-lift id = (s+j)*G + y.
    """
    d = P.shape[0]
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            g = int(V[k, i])
            nbr[i * G:(i + 1) * G, k] = s * G + int(P[k, i]) * G + T[:, g]
        for j in range(s):
            i = int(Pinv[k, j])
            g = int(V[k, i])
            nbr[(s + j) * G:(s + j + 1) * G, k] = i * G + T[:, inv[g]]
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    Left multiplication by the group is an automorphism transitive on each fibre,
    so checking the identity of each base fibre suffices.
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


def _anneal(s, G, T, inv, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, G, T, inv)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(G)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, G, T, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, G, T, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, key, P, V, d):
    """Materialise the group lift as (n, edges), deduplicated."""
    G, T, inv = _group_tables(key)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, G, T, inv)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _candidate_keys(gmax):
    """Map each order G in 2..gmax to its candidate groups: the cyclic group first, then semidirect ones."""
    cands = {G: [(G, 1, 1)] for G in range(2, gmax + 1)}
    for k in range(2, K_MAX + 1):
        for m in range(2, gmax // k + 1):
            G = m * k
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands[G].append((m, k, r))
    return cands


def _search_groups(s, d, D, rng, deadline, orders, cands):
    """Bisection over the sorted group orders for the largest G whose lift passes annealing.

    For each order, a few candidate groups are tried (cyclic first, then random semidirect ones).
    """
    best = None
    lo, hi = -1, len(orders)
    while lo + 1 < hi and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        G = orders[mid]
        keys = cands[G]
        nonab = list(keys[1:])
        rng.shuffle(nonab)
        tries = [keys[0]] + nonab[:2]
        found = None
        for key in tries:
            now = time.monotonic()
            if now >= deadline:
                break
            budget_end = min(deadline, now + max(0.2, 0.35 * (deadline - now)))
            _, T, inv = _group_tables(key)
            st = _anneal(s, G, T, inv, d, D, rng, budget_end)
            if st is not None:
                found = (key, st[0], st[1])
                break
        if found is not None:
            lo = mid
            best = (G, found[0], found[1], found[2])
        else:
            hi = mid
    return best


def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    q = x
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return q if q >= 2 else None


def _augment(n, edges, d, seed):
    """Add point-line edges between non-incident pairs using spare degree (points 0..n/2-1, lines n/2..n-1).

    Extra edges only shorten distances, so diameter and bipartiteness are preserved.
    """
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
    """W(q) incidence graph with q the largest prime power <= d-1 (degree q+1 <= d), plus spare-degree edges."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, edges = _gq_incidence(q)
    return _augment(n, edges, d, seed)


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

    # D >= 4: generalized quadrangle W(q) incidence graph (diameter 4), augmented with spare degree.
    gq = None
    if D >= 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            gq = cand

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # Candidate groups (cyclic and semidirect) for voltage lifts, indexed by order.
    cands = {}
    orders = []
    gmax = min(GMAX, cap // 2)
    if gmax >= 2:
        cands = _candidate_keys(gmax)
        orders = sorted(cands)

    best = None  # (n, s, key, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        gs = cap // (2 * s)
        ords = [G for G in orders if G <= gs]
        if not ords:
            continue
        res = _search_groups(s, d, D, rng, slice_end, ords, cands)
        if res is not None:
            G, key, P, V = res
            n = 2 * s * G
            if best is None or n > best[0]:
                best = (n, s, key, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    # Return the largest valid candidate.
    options = [c for c in (pg, gq, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
