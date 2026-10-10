import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 2500                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side (cyclic lifts)
G_S_LIST = (1, 2, 3, 4)       # number of base vertices per side (group lifts)
G_CAP = 600                   # largest group order used for non-abelian lifts


# ------------------------------------------------------------ cyclic lifts (Z_m)

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

    The group action is transitive on each fibre, so checking base-vertex sources suffices.
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
    """Simulated annealing over permutations and voltages for Z_m. Returns (P, V) or None."""
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
    """Materialise the cyclic lift as (n, edges), deduplicated."""
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
    """For fixed s, find the largest cyclic m (doubling then bisection) whose lift passes annealing."""
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


# ------------------------------------------- NEW: non-abelian semidirect lifts

def _semidirect_list(maxG):
    """All semidirect products Z_m x|_r Z_k with k >= 2 and order m*k <= maxG, largest first.

    Entries are (G, m, k, r). Requires gcd(r, m) = 1 and r^k = 1 mod m. r = 1 gives the direct product.
    """
    out = []
    for m in range(2, maxG + 1):
        for k in range(2, maxG // m + 1):
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((m * k, m, k, r))
    out.sort(key=lambda t: -t[0])
    return out


def _semidirect_tables(m, k, r):
    """Vectorised multiplication and inverse tables for Z_m x|_r Z_k.

    Element (a, b) is coded a*k+b, identity is 0. (a,b)(c,d) = (a + r^b c, b + d).
    Inverse of (a, b) is (-r^(-b) a, -b), using r^k = 1 mod m.
    """
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a, b = x // k, x % k
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    mul = A * k + B
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return mul, inv


def _neighbors_grp(P, Pinv, V, s, G, mul, inv):
    """Neighbour table of the group lift with left-invariant structure.

    A-vertex (i, x) joins B-vertex (j, x*g) for dart k with P[k,i]=j, V[k,i]=g.
    B-vertex (j, y) joins A-vertex (i, y*g^-1) for dart k with Pinv[k,j]=i.
    Left multiplication by any h is an automorphism, so identity sources suffice.
    """
    d = P.shape[0]
    x = np.arange(G, dtype=np.int64)
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * G:(i + 1) * G, k] = s * G + j * G + mul[x, int(V[k, i])]
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * G:(s + j + 1) * G, k] = i * G + mul[x, inv[int(V[k, i])]]
    return nbr


def _anneal_grp(s, G, mul, inv, d, D, rng, deadline):
    """Simulated annealing over base permutations and group voltages. Returns (P, V) or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors_grp(P, Pinv, V, s, G, mul, inv)
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
            cand = _neighbors_grp(P, Pinv, V, s, G, mul, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors_grp(P, Pinv, V, s, G, mul, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph_grp(s, G, mul, inv, P, V, d):
    """Materialise a group lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors_grp(P, Pinv, V, s, G, mul, inv)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _group_search(d, D, rng, deadline, cap):
    """Search semidirect lifts, largest group first for each base size s.

    Returns (n, s, G, mul, inv, P, V) for the largest successful lift, or None.
    """
    maxG = min(G_CAP, cap // 2)
    if maxG < 4:
        return None
    groups = _semidirect_list(maxG)
    best = None
    for idx, s in enumerate(G_S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(G_S_LIST) - idx)
        for G, m, k, r in groups:
            if 2 * s * G > cap:
                continue
            now = time.monotonic()
            if now >= slice_end:
                break
            attempt_end = min(slice_end, now + max(0.4, (slice_end - now) / 6.0))
            mul, inv = _semidirect_tables(m, k, r)
            st = _anneal_grp(s, G, mul, inv, d, D, rng, attempt_end)
            if st is not None:
                n = 2 * s * G
                if best is None or n > best[0]:
                    best = (n, s, G, mul, inv, st[0], st[1])
                break  # first success for this s is the largest for this s
    return best


# ------------------------------------------------------- projective / GQ based

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
    """W(q) incidence graph with q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, edges = _gq_incidence(q)
    return _augment(n, edges, d, seed)


# ------------------------------------------------------------------- driver

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

    # D >= 4: generalized quadrangle W(q) incidence graph, augmented with spare degree.
    gq = None
    if D >= 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            gq = cand

    if D < 2 or d < 1:
        return fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))

    # Cyclic lifts get a minority share of the budget.
    cyc_deadline = start + 0.3 * (deadline - start)
    best = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= cyc_deadline:
            break
        slice_end = now + (cyc_deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    # Non-abelian semidirect lifts get the rest of the budget.
    grp = None
    if d >= 2 and time.monotonic() < deadline:
        res = _group_search(d, D, rng, deadline, cap)
        if res is not None:
            _, s, G, mul, inv, P, V = res
            n, e = _graph_grp(s, G, mul, inv, P, V, d)
            if lib.is_valid(n, e, d, D):
                grp = (n, e)

    options = [c for c in (pg, gq, lift, grp, fallback) if c is not None]
    return max(options, key=lambda c: c[0])
