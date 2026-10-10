import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000            # hard cap on vertex count
ITERS = 1500            # annealing iterations per attempt
S_LIST = (1, 2, 3)      # base vertices per side
K_LIST = (1, 2, 3, 4)   # order of the acting cyclic factor Z_k in Z_m x| Z_k
R_PER_M = 3             # number of multipliers r tried per (s, k, m)


# ---------------------------------------------------------------- group Z_m x|_r Z_k
# Element (a, b) is coded as a*k + b.  (a,b)(c,e) = (a + r^b c, b + e).
# Left multiplication by any element is a graph automorphism of a group lift,
# so the Z-lift is vertex-transitive on each fibre (cost needs only base sources).

def _gmul(x, y, m, k, pw):
    """Vectorised group product x*y; x may be an array, y a scalar code (or array)."""
    a, b = np.divmod(x, k)
    c, e = np.divmod(y, k)
    return ((a + pw[b] * c) % m) * k + (b + e) % k


def _ginv(g, m, k, pw):
    """Inverse of group code g: (a,b)^-1 = (-r^(-b) a, -b)."""
    a, b = divmod(g, k)
    nb = (-b) % k
    return ((-int(pw[nb]) * a) % m) * k + nb


def _units(m, k):
    """All r in Z_m with gcd(r, m) = 1 and r^k = 1 (mod m)."""
    return [r for r in range(m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]


def _neighbors(G, P, s, M, m, k, pw):
    """Neighbour table (2sM x d) of the group lift of a d-regular bipartite base.

    Dart t joins A-vertex (i, x) to B-vertex (P[t,i], x*G[t,i]).
    A-id = i*M + x, B-id = (s+j)*M + y.
    """
    d = P.shape[0]
    Pinv = np.argsort(P, axis=1)
    x = np.arange(M, dtype=np.int64)
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for t in range(d):
        for i in range(s):
            j = int(P[t, i])
            nbr[i * M:(i + 1) * M, t] = (s + j) * M + _gmul(x, int(G[t, i]), m, k, pw)
        for j in range(s):
            i = int(Pinv[t, j])
            gi = _ginv(int(G[t, i]), m, k, pw)
            nbr[(s + j) * M:(s + j + 1) * M, t] = i * M + _gmul(x, gi, m, k, pw)
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M_ = R.copy()
        for t in range(nbr.shape[1]):
            M_ |= R[:, nbr[:, t]]
        if np.array_equal(M_, R):
            break
        R = M_
    return int(S * n - np.count_nonzero(R))


def _anneal(s, M, m, k, pw, d, D, rng, deadline):
    """Simulated annealing over base permutations and group voltages. Returns (P, G) or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    G = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * M for i in range(2 * s)]
    nbr = _neighbors(G, P, s, M, m, k, pw)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            t, i = rng.randrange(d), rng.randrange(s)
            old = int(G[t, i])
            new = rng.randrange(M)
            if new == old:
                continue
            G[t, i] = new
            cand = _neighbors(G, P, s, M, m, k, pw)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                G[t, i] = old
        else:
            t = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            P[t, a], P[t, b] = P[t, b], P[t, a]
            cand = _neighbors(G, P, s, M, m, k, pw)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                P[t, a], P[t, b] = P[t, b], P[t, a]
    if cur == 0:
        return P.copy(), G.copy()
    return None


def _graph(s, M, m, k, pw, P, G):
    """Materialise the group lift as (n, edges), deduplicated. A-side ids come first."""
    nbr = _neighbors(G, P, s, M, m, k, pw)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _feasible(s, m, k, d, D, rng, deadline):
    """Try a few multipliers r for this (s, k, m). Returns (pw, P, G) or None."""
    rs = _units(m, k)
    if not rs:
        return None
    rng.shuffle(rs)
    M = m * k
    for r in rs[:R_PER_M]:
        if time.monotonic() > deadline:
            break
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        st = _anneal(s, M, m, k, pw, d, D, rng, deadline)
        if st is not None:
            return pw, st[0], st[1]
    return None


def _search_family(s, k, d, D, rng, deadline, cap):
    """For fixed (s, k), find the largest m (doubling then bisection) with a valid lift."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m * k > cap:
            hi = m
        else:
            res = _feasible(s, m, k, d, D, rng, deadline)
            if res is not None:
                lo = m
                best = (m, res)
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ------------------------------------------------------------ projective / GQ bases

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    q = x
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return q if q >= 2 else None


def _augment(n, edges, d, seed):
    """Add bipartite edges between non-adjacent pairs using spare degree.

    Assumes vertices 0..n/2-1 form one side and n/2..n-1 the other.
    Adding edges never increases distances, so diameter and bipartiteness are kept.
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
    """Incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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


# ------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.6 * time_limit - 1.0)

    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])
    else:
        fallback = (1, [])

    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    gq = None
    if D >= 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            gq = cand

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    lift = None
    combos = [(s, k) for s in S_LIST for k in K_LIST]
    for idx, (s, k) in enumerate(combos):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(combos) - idx)
        res = _search_family(s, k, d, D, rng, slice_end, cap)
        if res is None:
            continue
        m, (pw, P, G) = res
        M = m * k
        n, e = _graph(s, M, m, k, pw, P, G)
        if lift is not None and n <= lift[0]:
            continue
        for cand in (_augment(n, e, d, seed), (n, e)):
            if lib.is_valid(cand[0], cand[1], d, D):
                lift = cand
                break

    options = [c for c in (pg, gq, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
