import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000          # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 3000          # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
KINDS = (0, 1)        # 0: cyclic Z_m (order m); 1: dihedral Z_m x| Z_2 with r = -1 (order 2m)


def _order(kind, m):
    """Order of the voltage group of the given kind and parameter m."""
    return m if kind == 0 else 2 * m


def _mul_right(kind, m, g, v):
    """Vector of products x*v over all group elements x = g (g is an int64 array of indices)."""
    if kind == 0:
        return (g + v) % m
    # Dihedral: element coded 2a+b, (a,b)*(c,d) = (a + r^b c, b + d), r = -1 mod m.
    a = g // 2
    b = g % 2
    va, vb = v // 2, v % 2
    pw = np.where(b == 1, (m - 1) % m, 1 % m)
    na = (a + pw * va) % m
    nb = (b + vb) % 2
    return 2 * na + nb


def _inv(kind, m, v):
    """Inverse of a single group element v."""
    if kind == 0:
        return (-v) % m
    va, vb = v // 2, v % 2
    r = (m - 1) % m if vb else 1 % m
    return 2 * ((-r * va) % m) + vb


def _neighbors(P, Pinv, V, s, kind, m):
    """Neighbour table (nM x d) of the group lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex (i, x) to B-vertex (P[k, i], x * V[k, i]). A-lift id = i*M + x,
    B-lift id = (s+j)*M + y, with M the group order.
    """
    M = _order(kind, m)
    d = P.shape[0]
    g = np.arange(M, dtype=np.int64)
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            v = int(V[k, i])
            nbr[i * M:(i + 1) * M, k] = s * M + j * M + _mul_right(kind, m, g, v)
        for j in range(s):
            i = int(Pinv[k, j])
            v = int(V[k, i])
            nbr[(s + j) * M:(s + j + 1) * M, k] = i * M + _mul_right(kind, m, g, _inv(kind, m, v))
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    Left multiplication by the group is an automorphism transitive on each fibre,
    so checking the base-vertex sources suffices.
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


def _anneal(s, kind, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    M = _order(kind, m)
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * M for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, kind, m)
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
            cand = _neighbors(P, Pinv, V, s, kind, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, kind, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)  # swapping the same positions again undoes it
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, kind, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    M = _order(kind, m)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, kind, m)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _search(s, kind, d, D, rng, deadline, cap):
    """For fixed s and group kind, find the largest m (by doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * _order(kind, m) > cap:
            hi = m
        else:
            st = _anneal(s, kind, m, d, D, rng, deadline)
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
            # Rejection sampling for a line with spare degree that is not incident to p.
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
        # Symplectic form B(a, y) = a0*y1 - a1*y0 + a2*y3 - a3*y2, vectorised over all points y.
        row = add[add[mul[a[0], pts[:, 1]], neg[mul[a[1], pts[:, 0]]]],
                  add[mul[a[2], pts[:, 3]], neg[mul[a[3], pts[:, 2]]]]]
        for j in np.nonzero(row == 0)[0].tolist():
            if j == i or j in covered[i]:
                continue
            # The totally isotropic line through i and j: points j and a + t*pts[j] (t in GF(q)).
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
    best = None  # (n, s, kind, m, P, V)
    # Search over (base size, group) pairs; dihedral groups are searched too, since
    # non-abelian voltage groups reach larger lifts than cyclic ones for many (d, D).
    combos = [(s, kind) for s in S_LIST for kind in KINDS]
    for idx, (s, kind) in enumerate(combos):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(combos) - idx)
        res = _search(s, kind, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * _order(kind, m)
            if best is None or n > best[0]:
                best = (n, s, kind, m, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], best[5], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    # Return the largest valid candidate.
    options = [c for c in (pg, gq, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
