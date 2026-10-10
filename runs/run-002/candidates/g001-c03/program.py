import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                       # hard cap on vertex count
ITERS = 3000                       # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)        # base vertices per side
K_LIST = (1, 2, 3, 4, 6)           # order of the second factor in Z_m x|_r Z_k


# ------------------------------------------------------------ group machinery

def _group_info(m, k, r):
    """Semidirect product Z_m x|_r Z_k (element (a, b) coded as a*k+b), as (order, vectorised mul, inverse codes).

    Matches lib.semidirect_group: (a, b)*(c, e) = (a + r^b c, b + e). Requires r^k = 1 mod m, gcd(r, m) = 1.
    """
    M = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(M, dtype=np.int64)
    A, B = X // k, X % k
    nb = (-B) % k
    invs = ((-powers[nb] * A) % m) * k + nb      # inverse of (a, b) is (-r^{-b} a, -b)

    def mulv(Xv, g):
        """Right multiplication of the array Xv by the single element g."""
        c, e = divmod(g, k)
        a, b = Xv // k, Xv % k
        return ((a + powers[b] * c) % m) * k + (b + e) % k

    return M, mulv, invs


def _gneighbors(P, Pinv, V, s, info):
    """Neighbour table (2*s*M x d) of the group lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex i to B-vertex P[k, i] with voltage V[k, i]: the A-lift vertex x*? is
    i*M + x and joins (s+j)*M + mul(x, g). Left translation by any group element is an automorphism,
    so the identity sources of the fibres suffice for the distance check.
    """
    M, mulv, invs = info
    d = P.shape[0]
    X = np.arange(M, dtype=np.int64)
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            g = int(V[k, i])
            nbr[i * M:(i + 1) * M, k] = s * M + j * M + mulv(X, g)
        for j in range(s):
            i = int(Pinv[k, j])
            ig = int(invs[int(V[k, i])])
            nbr[(s + j) * M:(s + j + 1) * M, k] = i * M + mulv(X, ig)
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


def _anneal_group(s, d, D, info, rng, deadline):
    """Simulated annealing over permutations and group voltages. Returns (P, V) with zero cost, or None."""
    M = info[0]
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * M for i in range(2 * s)]      # identity element of each fibre
    nbr = _gneighbors(P, Pinv, V, s, info)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(M)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _gneighbors(P, Pinv, V, s, info)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _gneighbors(P, Pinv, V, s, info)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph_group(s, info, P, V, d):
    """Materialise the group lift as (n, edges), deduplicated. A-side ids are below B-side ids."""
    M = info[0]
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _gneighbors(P, Pinv, V, s, info)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _try_group(s, m, k, d, D, rng, deadline):
    """Try a few random semidirect factors r for Z_m x|_r Z_k; return (r, info, P, V) or None."""
    if m < 2:
        return None
    rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    for _ in range(2):
        if time.monotonic() > deadline:
            break
        r = rng.choice(rs)
        info = _group_info(m, k, r)
        st = _anneal_group(s, d, D, info, rng, deadline)
        if st is not None:
            return (r, info, st[0], st[1])
    return None


def _search_group(s, k, d, D, rng, deadline, cap):
    """For fixed (s, k), find the largest m (doubling then bisection) whose group lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 2
    while time.monotonic() < deadline:
        if 2 * s * m * k > cap:
            hi = m
        else:
            res = _try_group(s, m, k, d, D, rng, deadline)
            if res is not None:
                lo = m
                best = (m, res[0], res[1], res[2], res[3])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ------------------------------------------------------------ D = 3 construction

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


# ------------------------------------------------------------ entry point

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
    best = None  # (n, s, info, P, V)

    # Search over (s, k) pairs; each pair picks semidirect factors Z_m x|_r Z_k.
    combos = [(s, k) for s in S_LIST for k in K_LIST]
    for idx, (s, k) in enumerate(combos):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(combos) - idx)
        res = _search_group(s, k, d, D, rng, slice_end, cap)
        if res is not None:
            m, r, info, P, V = res
            n = 2 * s * info[0]
            if best is None or n > best[0]:
                best = (n, s, info, P, V)

    lift = None
    if best is not None:
        n, e = _graph_group(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    options = [c for c in (pg, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
