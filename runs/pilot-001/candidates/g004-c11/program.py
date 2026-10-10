import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 3000                  # annealing iterations per attempt
ATTEMPTS = 3                  # fresh annealing restarts per (s, m) before declaring failure
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
PG_TRUST_N = 12000            # above this size, skip the expensive re-check of the PG construction
AUG_VERTEX_N = 1500           # only try vertex attachment below this size (is_valid is costly)
AUG_FAIL_LIMIT = 20           # stop vertex attachment after this many rejected attempts


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _augment(n, edges, d, D, rng, hard_deadline):
    """Use spare degree of a bipartite graph without breaking validity.

    Phase 1 adds edges between opposite-colour vertices that both have spare degree.
    Adding edges never increases distances and keeps the graph bipartite, so it is safe.
    Phase 2 attaches a new vertex of degree d to d spare opposite-colour vertices, and
    keeps the attachment only if lib.is_valid accepts the enlarged graph.
    Returns (n, edges); on any inconsistency the input is returned unchanged.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return n, edges
    E = [tuple(e) for e in edges]

    # Phase 1: greedy densification between spare opposite-colour vertices.
    side0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    side1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(side0)
    rng.shuffle(side1)
    for a in side0:
        if time.monotonic() > hard_deadline:
            return n, E
        if len(adj[a]) >= d:
            continue
        for b in side1:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                E.append((min(a, b), max(a, b)))

    # Phase 2: attach new vertices of degree d using spare capacity, validated exactly.
    if n > AUG_VERTEX_N:
        return n, E
    fails = 0
    while time.monotonic() < hard_deadline and fails < AUG_FAIL_LIMIT:
        c = rng.randrange(2)
        partners = [v for v in range(n) if color[v] == 1 - c and len(adj[v]) < d]
        if len(partners) < d:
            c = 1 - c
            partners = [v for v in range(n) if color[v] == 1 - c and len(adj[v]) < d]
            if len(partners) < d:
                break
        T = rng.sample(partners, d)
        E2 = E + [(min(n, t), max(n, t)) for t in T]
        if lib.is_valid(n + 1, E2, d, D):
            for t in T:
                adj[t].add(n)
            adj.append(set(T))
            color.append(c)
            E = E2
            n += 1
        else:
            fails += 1
    return n, E


def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]. A-lift id = i*m+g,
    B-lift id = (s+j)*m+h. Every lift vertex gets exactly one neighbour per dart.
    """
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
                _swap(P, Pinv, k, a, b)  # swapping the same positions again undoes it
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _anneal_restarts(s, m, d, D, rng, deadline):
    """Run several independent annealing attempts at the same m while time remains."""
    for _ in range(ATTEMPTS):
        if time.monotonic() >= deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
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
            st = _anneal_restarts(s, m, d, D, rng, deadline)
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    hard_deadline = start + max(0.8, 0.9 * time_limit - 1.0)
    rng = random.Random(seed)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if D < 2 or d < 1:
        return fallback

    best = fallback

    # D = 3: incidence graph of PG(2, q), q the largest prime power <= d - 1.
    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best[0]:
            ok = pg[0] > PG_TRUST_N or lib.is_valid(pg[0], pg[1], d, D)
            if ok:
                best = pg
                # When d - 1 is a prime power this meets the Moore bound: nothing to gain.
                if lib.is_prime_power(d - 1):
                    return best
                # Otherwise spend leftover degree: densify and attach extra vertices.
                n_aug, e_aug = _augment(pg[0], pg[1], d, D, rng, hard_deadline)
                if n_aug > best[0] and lib.is_valid(n_aug, e_aug, d, D):
                    best = (n_aug, e_aug)

    # General D: voltage-lift search over Z_m with s base vertices per side.
    if d >= 2:
        cap = min(N_CAP, lib._moore_bound(d, D))
        lift = None  # (n, s, m, P, V)
        for idx, s in enumerate(S_LIST):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_end = now + (deadline - now) / (len(S_LIST) - idx)
            res = _search(s, d, D, rng, slice_end, cap)
            if res is not None:
                m, P, V = res
                n = 2 * s * m
                if lift is None or n > lift[0]:
                    lift = (n, s, m, P, V)
        if lift is not None and lift[0] > best[0]:
            n, e = _graph(lift[1], lift[2], lift[3], lift[4], d)
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                n_aug, e_aug = _augment(n, e, d, D, rng, hard_deadline)
                if n_aug > best[0] and lib.is_valid(n_aug, e_aug, d, D):
                    best = (n_aug, e_aug)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
