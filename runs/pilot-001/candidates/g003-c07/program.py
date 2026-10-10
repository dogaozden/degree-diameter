import math
import random
import time

import numpy as np

import lib

N_CAP = 6000          # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 3000          # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side


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


def _perfect_matching(left_adj, nl):
    """Return match_l (list: left i -> right j) forming a perfect matching, or None.

    Uses BFS augmenting paths (iterative, no recursion limit issues)."""
    match_l = [-1] * nl
    match_r = [-1] * nl
    for u in range(nl):
        prev = {}
        seen_l = {u}
        queue = [u]
        found = None
        qi = 0
        while qi < len(queue) and found is None:
            x = queue[qi]
            qi += 1
            for y in left_adj[x]:
                if y in prev:
                    continue
                prev[y] = x
                if match_r[y] == -1:
                    found = y
                    break
                z = match_r[y]
                if z not in seen_l:
                    seen_l.add(z)
                    queue.append(z)
        if found is None:
            return None
        y = found
        while True:
            x = prev[y]
            nxt = match_l[x]
            match_l[x] = y
            match_r[y] = x
            if x == u:
                break
            y = nxt
    return match_l


def _pg_with_matchings(d):
    """PG(2,q) incidence graph with q+1 <= d, plus r = d-(q+1) extra perfect matchings
    on non-incident point-line pairs. Adding edges never increases distances, so diameter 3 holds.
    Returns (n, edges) or None."""
    q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
    if q is None:
        return None
    n0 = 2 * (q * q + q + 1)
    if n0 > N_CAP:
        return None
    r = d - (q + 1)
    n0, e0 = lib.projective_plane_incidence(q)
    m = n0 // 2
    used = [set() for _ in range(m)]
    edges = list(e0)
    for u, v in e0:
        used[u].add(v - m)
    for _ in range(r):
        left_adj = [[j for j in range(m) if j not in used[i]] for i in range(m)]
        match = _perfect_matching(left_adj, m)
        if match is None:
            return None
        for i, j in enumerate(match):
            used[i].add(j)
            edges.append((i, m + j))
    return n0, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use most of the allowed time for the search. Leave a margin for the final
    # lib.is_valid check and for slower machines.
    deadline = start + max(0.5, 0.8 * time_limit - 1.5)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        best = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        best = (2, [(0, 1)])                     # K_2
    else:
        best = (1, [])

    # D = 3 constructions from projective planes.
    if D == 3 and d >= 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        res = _pg_with_matchings(d)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if D < 2 or d < 1:
        return best

    rng = random.Random(seed)
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
            return n, e
    return best
