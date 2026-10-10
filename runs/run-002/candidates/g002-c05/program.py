import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                     # hard cap on vertex count
S_LIST = (1, 2, 3, 4, 5, 6)      # base vertices per side
ITERS = 2500                     # annealing iterations per attempt


# ---------------------------------------------------------------- projective / GQ constructions

def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    q = x
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return q if q >= 2 else None


def _augment(n, edges, d, seed):
    """Add edges between non-incident point/line pairs using spare degree (points 0..n/2-1, lines n/2..n-1).

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
    """Incidence graph of PG(2,q), q the largest prime power <= d-1, plus spare-degree edges."""
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
    """W(q) incidence graph, q the largest prime power <= d-1, plus spare-degree edges."""
    q = _largest_pp(d - 1)
    if q is None:
        return None
    n, edges = _gq_incidence(q)
    return _augment(n, edges, d, seed)


# ---------------------------------------------------------------- semidirect-product lifts

def _pw(m, k, r):
    """pw[b] = r^b mod m for b in 0..k-1 (right-multiplication helper)."""
    return np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)


def _nbr(P, Pinv, V, s, N, m, k, pw, d):
    """Neighbour table (2*s*N x d) of the lift of a d-regular bipartite base on s+s vertices over G = Z_m x|_r Z_k.

    Group element g = c*k + e is the pair (c, e); product (a,b)(c,e) = (a + r^b c, b + e).
    A-vertex (i, x) -> index i*N + x; B-vertex (j, y) -> index (s+j)*N + y.
    Dart kk joins A-vertex (i, x) to B-vertex (P[kk,i], x*g) with g = V[kk,i].
    """
    nbr = np.empty((2 * s * N, d), dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    for kk in range(d):
        for i in range(s):
            c, e = divmod(int(V[kk, i]), k)
            j = int(P[kk, i])
            img = ((a + pw[b] * c) % m) * k + (b + e) % k
            nbr[i * N:(i + 1) * N, kk] = (s + j) * N + img
        for j in range(s):
            i = int(Pinv[kk, j])
            c, e = divmod(int(V[kk, i]), k)
            ei = (-e) % k
            ci = (-int(pw[ei]) * c) % m          # inverse of (c, e) is (-r^{-e} c, -e)
            img = ((a + pw[b] * ci) % m) * k + (b + ei) % k
            nbr[(s + j) * N:(s + j + 1) * N, kk] = i * N + img
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    The group acts transitively on each fibre (by left multiplication), so base sources suffice.
    """
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for kk in range(nbr.shape[1]):
            M |= R[:, nbr[:, kk]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, kk, a, b):
    P[kk, a], P[kk, b] = P[kk, b], P[kk, a]
    Pinv[kk, P[kk, a]] = a
    Pinv[kk, P[kk, b]] = b


def _anneal(s, m, k, r, d, D, rng, deadline):
    """Simulated annealing over base permutations and group voltages. Returns (P, V) or None."""
    N = m * k
    pw = _pw(m, k, r)
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for kk in range(d):
        for i in range(s):
            Pinv[kk, P[kk, i]] = i
    V = np.array([[rng.randrange(N) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [v * N for v in range(2 * s)]
    cur_nbr = _nbr(P, Pinv, V, s, N, m, k, pw, d)
    cur = _cost(cur_nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            kk, i = rng.randrange(d), rng.randrange(s)
            old = int(V[kk, i])
            new = rng.randrange(N)
            if new == old:
                continue
            V[kk, i] = new
            cand = _nbr(P, Pinv, V, s, N, m, k, pw, d)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, cur_nbr = c, cand
            else:
                V[kk, i] = old
        else:
            kk = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, kk, a, b)
            cand = _nbr(P, Pinv, V, s, N, m, k, pw, d)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, cur_nbr = c, cand
            else:
                _swap(P, Pinv, kk, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _edges(P, V, s, m, k, r, d):
    """Materialise the lift as (n, edges), deduplicated. Degree stays <= d, graph stays bipartite."""
    N = m * k
    pw = _pw(m, k, r)
    Pinv = np.zeros_like(P)
    for kk in range(d):
        for i in range(s):
            Pinv[kk, P[kk, i]] = i
    nbr = _nbr(P, Pinv, V, s, N, m, k, pw, d)
    edges = set()
    for x in range(s * N):              # every edge has exactly one endpoint in the A-side
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * N, sorted(edges)


def _group_search(d, D, cap, rng, deadline, best):
    """Random search over (s, group Z_m x|_r Z_k, base, voltages) for lifts beating `best`."""
    while time.monotonic() < deadline:
        best_n = best[0]
        opts = [s for s in S_LIST if cap // (2 * s) > best_n // (2 * s)]
        if not opts:
            break
        s = rng.choice(opts)
        lo = best_n // (2 * s)
        hi = cap // (2 * s)
        # Bias toward orders just above the current best.
        N = lo + 1 + int((hi - lo) * rng.random() ** 2)
        N = min(max(N, lo + 1), hi)
        divs = set()
        t = 1
        while t * t <= N:
            if N % t == 0:
                divs.add(t)
                divs.add(N // t)
            t += 1
        m = rng.choice(sorted(divs))
        k = N // m
        if m == 1:
            r = 0
        else:
            r = 1
            if rng.random() < 0.7:
                for _ in range(60):
                    cand = rng.randrange(1, m)
                    if math.gcd(cand, m) == 1 and pow(cand, k, m) == 1 % m:
                        r = cand
                        break
        now = time.monotonic()
        budget = min(deadline - now, 2.0)
        if budget <= 0:
            break
        res = _anneal(s, m, k, r, d, D, rng, now + budget)
        if res is not None:
            P, V = res
            n, e = _edges(P, V, s, m, k, r, d)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    return best


# ---------------------------------------------------------------- main entry

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.7 * time_limit - 1.0)

    # Trivial fallbacks.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if D < 2 or d < 1:
        return fallback

    best = fallback

    # D = 3: projective plane incidence graph (optimal when d-1 is a prime power).
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
            if lib.is_prime_power(d - 1):
                return best

    # D >= 4: generalized quadrangle incidence graph (diameter 4).
    if D >= 4 and d >= 3:
        cand = _gq_augmented(d, seed)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    # Bold change: search non-cyclic semidirect-product lifts (Z_m x|_r Z_k) of small base graphs.
    cap = min(N_CAP, lib._moore_bound(d, D))
    rng = random.Random(seed)
    if cap >= 4:
        best = _group_search(d, D, cap, rng, deadline, best)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return fallback

