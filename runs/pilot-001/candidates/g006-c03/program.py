import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count (keeps is_valid fast and memory small)
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GQ_Q_MAX = 8                  # largest q for which W(q) is built (keeps construction fast)
RETRIES = 2                   # annealing attempts per candidate lift size before giving up


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


# ---------------------------------------------------------------- lifts (annealing)

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


# ---------------------------------------------------------------- random bipartite + edge-switch annealing

def _bad_pairs(n, adj, D):
    """Ordered count of vertex pairs at distance > D (unreachable counts as bad), via bitsets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                changed = True
            new.append(r)
        reach = new
        if not changed:
            break
    return sum(n - r.bit_count() for r in reach)


def _random_bip(m, d, rng):
    """Near d-regular simple bipartite edge set on A = 0..m-1, B = m..2m-1 from random matchings."""
    eset = set()
    for _ in range(d):
        for _try in range(40):
            perm = list(range(m, 2 * m))
            rng.shuffle(perm)
            pairs = [(i, perm[i]) for i in range(m)]
            if not any(p in eset for p in pairs):
                eset.update(pairs)
                break
    return eset


def _anneal_bip(m, d, D, rng, deadline):
    """Edge-switch annealing on a random bipartite graph with m+m vertices. Returns edge list or None."""
    n = 2 * m
    eset = _random_bip(m, d, rng)
    edges = list(eset)
    if len(edges) < 2:
        return None
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    cur = _bad_pairs(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    E = len(edges)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = 1.5 * (1.0 - frac) + 0.05
        i, j = rng.randrange(E), rng.randrange(E)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        # apply switch a1-b1, a2-b2 -> a1-b2, a2-b1
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        c = _bad_pairs(n, adj, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            edges[i] = (a1, b2)
            edges[j] = (a2, b1)
        else:
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    if cur == 0:
        return list(edges)
    return None


def _grow(d, D, seed, deadline, n_start, nmax):
    """Search for the largest m such that the random-bipartite annealing reaches zero bad pairs."""
    rng = random.Random(seed * 7919 + 13)
    best = None
    lo = None
    hi = None
    m = max(d, (n_start // 2) * 105 // 100 + 1)
    attempts = 0
    while time.monotonic() < deadline and attempts < 40:
        attempts += 1
        if 2 * m > nmax:
            m = max(d, nmax // 2)
            if lo is not None and m <= lo:
                break
        if lo is not None and hi is not None and hi - lo <= 1:
            break
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + max(0.5, remaining * 0.4)
        res = _anneal_bip(m, d, D, rng, min(slice_end, deadline))
        if res is not None:
            lo = m
            best = (2 * m, res)
        else:
            hi = m
        prev = m
        if lo is None:
            m = max(d, int(m * 0.9))
            if m >= prev:
                break
        elif hi is None:
            m = int(lo * 1.1) + 1
        else:
            m = (lo + hi) // 2
            if m == lo:
                break
    return best


# ---------------------------------------------------------------- parent pipeline (unchanged logic)

def _parent_build(d, D, seed, time_limit):
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
    t0 = time.monotonic()
    total = float(time_limit)

    # Weak cases (large degree at D=5, larger degree at D=4, big degree at D=3): bold change.
    weak = (D >= 5 and d >= 4) or (D == 4 and d >= 7) or (D == 3 and d >= 11)
    if not weak or d < 3:
        return _parent_build(d, D, seed, total)

    # Safe baseline from the parent pipeline with a reduced budget.
    base = _parent_build(d, D, seed, 0.4 * total)
    best = base

    # New construction: random near-regular bipartite graph, grown and repaired by edge switches.
    deadline = t0 + max(1.0, 0.72 * total - 1.0)
    nmax = min(2000, lib._moore_bound(d, D))
    try:
        res = _grow(d, D, seed, deadline, base[0], nmax)
        if res is not None:
            n, edges = res[0], res[1]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
    except Exception:
        pass

    return best
