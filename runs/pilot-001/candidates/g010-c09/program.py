import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side


# ----------------------------------------------------------- lift search (unchanged idea)

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


# ------------------------------------------------- helpers shared by the algebraic builds

def _largest_prime_power_leq(x, n_cap_fn=None):
    """Largest prime power q with 2 <= q <= x (and optionally n_cap_fn(q) True), else None."""
    q = x
    while q >= 2:
        if lib.is_prime_power(q) and (n_cap_fn is None or n_cap_fn(q)):
            return q
        q -= 1
    return None


def _augment(n, m, edges, d, seed, passes=3):
    """Add point-line edges between non-incident pairs of spare degree.

    Vertices 0..m-1 are one side, m..n-1 the other side. Extra cross edges only shorten
    distances, so diameter and bipartiteness are preserved; degree is kept at most d.
    """
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    rng = random.Random(seed)
    new_edges = list(edges)
    for _ in range(passes):
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


# ----------------------------------------------------------- D = 3: projective plane

def _pg_candidate(d, seed):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_prime_power_leq(d - 1)
    if q is None:
        return None
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    return _augment(n, m, edges, d, seed)


# -------------------------------- D >= 4 (NEW): generalized quadrangle W(q) incidence graph

def _gq_incidence(q):
    """Incidence graph of the generalized quadrangle W(q) (symplectic W(3,q)).

    Points: all points of PG(3,q). Lines: totally isotropic lines of the symplectic form
    x0*y1 - x1*y0 + x2*y3 - x3*y2. Returns (n, m, edges) with points 0..m-1 and lines m..2m-1,
    or None on any inconsistency. The incidence graph is (q+1)-regular, bipartite, diameter 4.
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)

    def normalize(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    def isotropic(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        t = F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))
        return t == 0

    covered = set()  # point pairs (i, j), i < j, already lying on a found line
    lines = []
    for i in range(m):
        p = pts[i]
        for j in range(i + 1, m):
            if (i, j) in covered:
                continue
            x = pts[j]
            if not isotropic(p, x):
                continue
            members = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, p[t]), F.mul(b, x[t])) for t in range(4))
                    members.add(index[normalize(v)])
            mem = sorted(members)
            if len(mem) != q + 1:
                return None
            for u, w in itertools.combinations(mem, 2):
                covered.add((u, w))
            lines.append(mem)
    if len(lines) != (q + 1) * (q * q + 1):
        return None
    edges = [(P, m + L) for L, mem in enumerate(lines) for P in mem]
    return 2 * m, m, edges


def _gq_candidate(d, seed):
    """W(q) with q the largest prime power with q+1 <= d and modest order, plus spare degree."""
    q = _largest_prime_power_leq(
        d - 1, lambda qq: 2 * (qq + 1) * (qq * qq + 1) <= N_CAP)
    if q is None:
        return None
    built = _gq_incidence(q)
    if built is None:
        return None
    n, m, edges = built
    return _augment(n, m, edges, d, seed)


# ----------------------------------------------------------------------- build

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

    cands = [fallback]

    if D == 3 and d >= 3:
        pg = _pg_candidate(d, seed)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            cands.append(pg)
            if lib.is_prime_power(d - 1):
                return pg

    if D >= 4 and d >= 3:
        gq = _gq_candidate(d, seed)
        if gq is not None and lib.is_valid(gq[0], gq[1], d, D):
            cands.append(gq)

    if D < 2 or d < 1:
        return max(cands, key=lambda c: c[0])

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

    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            cands.append((n, e))

    return max(cands, key=lambda c: c[0])
