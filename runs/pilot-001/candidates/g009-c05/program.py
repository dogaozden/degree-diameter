import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 6000                  # annealing iterations per attempt (legacy voltage lifts)
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side (legacy voltage lifts)
GQ_Q_MAX = 8                  # largest q for which W(q) is built (keeps construction fast)
RETRIES = 2                   # annealing attempts per candidate lift size before giving up

# New construction: bi-Cayley (Haar-type) graphs over general abelian groups Z_a x Z_b.
# Vertices A = G and B = G; a_x ~ b_{x+s} for s in a d-subset S of G. Every vertex has
# degree d, the graph is bipartite, and translations act transitively on each side, so
# diameter <= D only needs checking from a_0 and b_0. Searched by simulated annealing over S.
ITERS2 = 1200                 # annealing iterations per abelian-group attempt
RETRIES2 = 2                  # attempts for the cyclic group Z_m
ABEL_GROUP_TRIES = 3          # extra non-cyclic groups Z_a x Z_b tried per order m


# ---------------------------------------------------------------- D = 3 : projective plane

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


# ---------------------------------------------------------------- D = 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- new: abelian bi-Cayley search

def _abel_nbr(X, Y, a, b, S):
    """Neighbour table (2m x d) for the bi-Cayley graph over Z_a x Z_b with connection set S.

    Element (x, y) has index x*b + y. A-vertex i (row i) joins B-vertex index(i + s);
    B-vertex j (row m + j) joins A-vertex index(j - s). Rows of B hold A-indices.
    """
    m = a * b
    nbr = np.empty((2 * m, len(S)), dtype=np.int64)
    for k, s in enumerate(S):
        sx, sy = s // b, s % b
        nbr[:m, k] = m + ((X + sx) % a) * b + (Y + sy) % b
        nbr[m:, k] = ((X - sx) % a) * b + (Y - sy) % b
    return nbr


def _abel_cost(nbr, m, D):
    """Number of (source, vertex) pairs NOT within distance D; sources are A-vertex 0 and B-vertex 0."""
    n = 2 * m
    d = nbr.shape[1]
    R = np.zeros((2, n), dtype=bool)
    R[0, 0] = True
    R[1, m] = True
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return 2 * n - int(np.count_nonzero(R))


def _abel_anneal(a, b, d, D, rng, deadline):
    """Anneal a connection set S (d distinct elements of Z_a x Z_b). Returns list S or None."""
    m = a * b
    idx = np.arange(m, dtype=np.int64)
    X, Y = idx // b, idx % b
    S = rng.sample(range(m), d)
    nbr = _abel_nbr(X, Y, a, b, S)
    cur = _abel_cost(nbr, m, D)
    for it in range(ITERS2):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / ITERS2) + 0.05
        k = rng.randrange(d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[k]
        S[k] = new
        cand = _abel_nbr(X, Y, a, b, S)
        c = _abel_cost(cand, m, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur, nbr = c, cand
        else:
            S[k] = old
    if cur == 0:
        return list(S)
    return None


def _try_order(m, d, D, rng, deadline):
    """Try to find a valid bi-Cayley graph on a group of order m. Returns (a, b, S) or None."""
    if m < d:
        return None
    divs = [x for x in range(1, math.isqrt(m) + 1) if m % x == 0]
    rest = divs[1:]
    rng.shuffle(rest)
    order = [(1, RETRIES2)] + [(x, 1) for x in rest[:ABEL_GROUP_TRIES]]
    for a, tries in order:
        b = m // a
        for _ in range(tries):
            if time.monotonic() > deadline:
                return None
            S = _abel_anneal(a, b, d, D, rng, deadline)
            if S is not None:
                return (a, b, S)
    return None


def _abel_graph(a, b, S):
    """Materialise the bi-Cayley graph as (n, edges)."""
    m = a * b
    idx = np.arange(m, dtype=np.int64)
    X, Y = idx // b, idx % b
    edges = []
    for s in S:
        sx, sy = s // b, s % b
        j = (((X + sx) % a) * b + (Y + sy) % b).tolist()
        for i in range(m):
            edges.append((i, m + j[i]))
    return 2 * m, edges


def _abelian_best(d, D, seed, deadline):
    """Largest valid bi-Cayley graph found before the deadline, as (n, edges), or None."""
    rng = random.Random(seed * 7919 + 13)
    moore = lib._moore_bound(d, D)
    cap_m = min(N_CAP // 2, moore // 2)
    if cap_m < d:
        return None
    lo, hi = 0, cap_m + 1
    best = None
    m = max(d, 2)
    while hi - lo > 1 and time.monotonic() < deadline:
        m = min(max(m, lo + 1), hi - 1)
        res = _try_order(m, d, D, rng, deadline)
        if res is not None:
            lo = m
            best = (m,) + res
            if hi > cap_m:
                m = min(2 * m, cap_m)      # still doubling
            else:
                m = (lo + hi) // 2
        else:
            hi = m
            m = (lo + hi) // 2
    if best is None:
        return None
    _, a, b, S = best
    return _abel_graph(a, b, S)


# ---------------------------------------------------------------- lifts (annealing, legacy)

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


def _try_size(s, m, d, D, rng, deadline):
    """Attempt to anneal a valid lift of size m, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (by doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try_size(s, m, d, D, rng, deadline)
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


# ---------------------------------------------------------------- legacy driver

def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if d < 1 or D < 1:
        return fallback if d >= 1 else (1, [])
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if d == 1:
        return (2, [(0, 1)])

    best = fallback

    def consider(c):
        nonlocal best
        if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c

    # D = 3: projective plane PG(2,q), q the largest prime power <= d-1, augmented with spare degree.
    if D == 3 and d >= 3:
        pg = _pg_augmented(d, seed)
        if pg is not None:
            consider(pg)
            if lib.is_prime_power(d - 1) and best is pg:
                return best

    # D >= 4: generalized quadrangle W(q), diameter 4 <= D.
    if D >= 4:
        consider(_best_gq(d))

    # Voltage-lift annealing for all D >= 2 (covers D = 3, 5, and any leftover budget).
    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    best_lift = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best_lift is None or n > best_lift[0]:
                best_lift = (n, s, m, P, V)

    if best_lift is not None:
        n, e = _graph(best_lift[1], best_lift[2], best_lift[3], best_lift[4], d)
        consider((n, e))

    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Always-valid fallback.
    if d >= 1 and D >= 2:
        best = lib.haar_graph(d, range(d))          # K_{d,d}: diameter 2
    elif d >= 1 and D >= 1:
        best = (2, [(0, 1)])
    else:
        best = (1, [])

    # Stage 1: bi-Cayley graphs over abelian groups (new construction), short budget.
    if d >= 2 and D >= 3:
        new_deadline = start + max(0.3, 0.4 * time_limit - 0.5)
        try:
            res = _abelian_best(d, D, seed, new_deadline)
        except Exception:
            res = None
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    # Stage 2: legacy pipeline (projective plane, quadrangle, voltage lifts) with the remaining budget.
    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed
    if remaining >= 1.5:
        try:
            leg = _legacy_build(d, D, seed, remaining)
        except Exception:
            leg = None
        if leg is not None and leg[0] > best[0] and lib.is_valid(leg[0], leg[1], d, D):
            best = leg

    return best
