import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
ATTEMPT_FRAC = 0.3            # fraction of remaining time given to one annealing attempt
ATTEMPT_MIN = 0.2             # seconds; lower bound on one attempt's budget


# ---------------------------------------------------------------- group lifts
# Voltages live in a finite abelian group Z_a x Z_b (not only the cyclic group Z_M).
# Elements are indexed g = x*b + y. Translations are automorphisms of the lift, so the
# cost function only needs base sources.

def _group_shapes(M):
    """Return group shapes (a, b) with a*b = M to try: the cyclic one and the most balanced one."""
    shapes = [(1, M)]
    best = None
    for a in range(2, math.isqrt(M) + 1):
        if M % a == 0:
            best = a
    if best is not None:
        shapes.append((best, M // best))
    return shapes


def _nbr(P, Pinv, V, s, a, b):
    """Neighbour table (n x d) of the Z_a x Z_b lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex (i, g) to B-vertex (P[k,i], g+v) with v = V[k,i]. Vertex ids:
    A-lift (i, g) -> i*M+g, B-lift (j, h) -> (s+j)*M+h, with M = a*b.
    """
    M = a * b
    d = P.shape[0]
    G = np.arange(M, dtype=np.int64)
    GX, GY = G // b, G % b
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            v = int(V[k, i])
            vx, vy = v // b, v % b
            tgt = ((GX + vx) % a) * b + (GY + vy) % b
            nbr[i * M:(i + 1) * M, k] = s * M + j * M + tgt
        for j in range(s):
            i = int(Pinv[k, j])
            v = int(V[k, i])
            vx, vy = v // b, v % b
            tgt = ((GX - vx) % a) * b + (GY - vy) % b
            nbr[(s + j) * M:(s + j + 1) * M, k] = i * M + tgt
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


def _anneal(s, a, b, d, D, rng, deadline):
    """Simulated annealing over permutations and group voltages.

    The run is limited by wall-clock time, not by a fixed iteration count. The temperature
    cools with the fraction of the time budget used, so a short attempt still gets a full
    cooling schedule. Returns (P, V) with zero cost, or None.
    """
    M = a * b
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * M for i in range(2 * s)]
    nbr = _nbr(P, Pinv, V, s, a, b)
    cur = _cost(nbr, sources, D)

    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while True:
        now = time.monotonic()
        if cur == 0 or now > deadline:
            break
        frac = min(1.0, (now - t0) / span)
        temp = 2.0 * (1.0 - frac) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(M)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _nbr(P, Pinv, V, s, a, b)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            x, y = rng.sample(range(s), 2)
            _swap(P, Pinv, k, x, y)
            cand = _nbr(P, Pinv, V, s, a, b)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, x, y)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, a, b, P, V, d):
    """Materialise the group lift as (n, edges), deduplicated."""
    M = a * b
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _nbr(P, Pinv, V, s, a, b)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest group order M (doubling then bisection) with a passing lift.

    Each annealing attempt gets a bounded share of the remaining time, so one hard order
    cannot starve the search for the others. For each order M, every group shape Z_a x Z_b
    (a*b = M) is tried. Returns (a, b, P, V) for the best order found, or None.
    """
    best = None
    lo, hi = 0, None
    M = 1
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            hi = M
        else:
            res = None
            for a, b in _group_shapes(M):
                now = time.monotonic()
                if now >= deadline:
                    break
                att = min(deadline, now + max(ATTEMPT_MIN, ATTEMPT_FRAC * (deadline - now)))
                st = _anneal(s, a, b, d, D, rng, att)
                if st is not None:
                    res = (a, b, st[0], st[1])
                    break
            if res is not None:
                lo = M
                best = res
            else:
                hi = M
        if hi is None:
            M = 2 * lo
        else:
            if hi - lo <= 1:
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- D = 3 base

def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges.

    Extra point-line edges between non-incident pairs only shorten distances, so diameter 3
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
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

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
    best = None  # (n, s, a, b, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            a, b, P, V = res
            n = 2 * s * a * b
            if best is None or n > best[0]:
                best = (n, s, a, b, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], best[5], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    options = [c for c in (pg, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
