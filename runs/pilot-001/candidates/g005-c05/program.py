import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side (voltage lifts)


# ---------------------------------------------------------------- voltage lifts (parent method)

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


# ---------------------------------------------------- edge-switch annealing (new method)

def _dense_cost(nbr, n, d, D):
    """Ordered (source, vertex) pairs not within distance D, for a general bipartite table."""
    tab = np.array(nbr, dtype=np.int64)
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[:, tab[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return n * n - int(np.count_nonzero(R))


def _switch(nbr, a1, k1, a2, k2):
    """Double edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps degrees and simplicity.

    Applying the same call again undoes it. Returns False (no change) if illegal.
    Table layout: A vertices are 0..m-1, B vertices are m..2m-1; nbr[v] lists neighbours of v.
    """
    b1 = nbr[a1][k1]
    b2 = nbr[a2][k2]
    if a1 == a2 or b1 == b2 or b2 in nbr[a1] or b1 in nbr[a2]:
        return False
    nbr[a1][k1] = b2
    nbr[a2][k2] = b1
    r = nbr[b1]
    r[r.index(a1)] = a2
    r = nbr[b2]
    r[r.index(a2)] = a1
    return True


def _haar_lists(m, d):
    """Haar graph with shifts 0..d-1 as an adjacency table (requires m >= d)."""
    nbr = [[0] * d for _ in range(2 * m)]
    for i in range(m):
        for s in range(d):
            j = (i + s) % m
            nbr[i][s] = m + j
            nbr[m + j][s] = i
    return nbr


def _anneal_switch(m, d, D, rng, deadline, t0, t1):
    """Anneal edge switches on a d-regular bipartite graph with m+m vertices.

    Returns the adjacency table if every pair is within distance D, else None.
    """
    n = 2 * m
    nbr = _haar_lists(m, d)
    cur = _dense_cost(nbr, n, d, D)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - start) / span)
        T = t0 + (t1 - t0) * frac
        a1, a2 = rng.sample(range(m), 2)
        k1, k2 = rng.randrange(d), rng.randrange(d)
        if not _switch(nbr, a1, k1, a2, k2):
            continue
        c = _dense_cost(nbr, n, d, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            if not _switch(nbr, a1, k1, a2, k2):  # undo; must succeed
                return None
    return nbr if cur == 0 else None


def _search_switch(d, D, rng, deadline, cap_m):
    """Grow m geometrically while annealing succeeds, then bisect. Returns (m, nbr) or None."""
    best = None
    lo, hi = None, None
    m = max(d, 2)
    while time.monotonic() < deadline and m <= cap_m:
        now = time.monotonic()
        slice_end = min(deadline, now + max(0.3, 0.35 * (deadline - now)))
        res = _anneal_switch(m, d, D, rng, slice_end, 3.0, 0.2)
        if res is not None:
            best = (m, res)
            lo = m
            m = max(m + 1, int(m * 1.15) + 1)
        else:
            hi = m
            break
    if lo is None or hi is None:
        return best
    while hi - lo > 1 and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        now = time.monotonic()
        slice_end = min(deadline, now + max(0.3, 0.5 * (deadline - now)))
        res = _anneal_switch(mid, d, D, rng, slice_end, 3.0, 0.2)
        if res is not None:
            best = (mid, res)
            lo = mid
        else:
            hi = mid
    return best


# ------------------------------------------------------------------ D = 3 base (parent)

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


# ------------------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.65 * time_limit - 0.5)
    deadline = start + total

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    candidates = [fallback]

    # D = 3: projective-plane construction (exact when d-1 is a prime power).
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            if lib.is_prime_power(d - 1):
                return cand
            candidates.append(cand)

    if D < 2 or d < 1:
        return max(candidates, key=lambda c: c[0])

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # New method: edge-switch annealing on a d-regular bipartite graph (60% of the budget).
    if d >= 2:
        anneal_end = start + 0.6 * total
        cap_m = cap // 2
        if cap_m >= max(d, 2):
            res = _search_switch(d, D, rng, anneal_end, cap_m)
            if res is not None:
                m, nbr = res
                n = 2 * m
                edges = [(a, nbr[a][k]) for a in range(m) for k in range(d)]
                if lib.is_valid(n, edges, d, D):
                    candidates.append((n, edges))

    # Parent method: voltage lifts with the remaining budget.
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

    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            candidates.append((n, e))

    # Return the largest valid candidate (fallback is always valid).
    return max(candidates, key=lambda c: c[0])
