import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # cyclic annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # base vertices per side for cyclic lifts
GQ_Q_MAX = 9                  # largest q for which W(q) is built
RETRIES = 2                   # annealing attempts per candidate size
TIME_FRAC = 0.6               # fraction of time_limit for the main search
POST_FRAC = 0.72              # fraction of time_limit after which post-processing stops
ILS_FRAC = 0.8                # fraction of time_limit after which iterated search stops
GROW_SLICE = 0.5              # seconds per greedy growth variant
POST_LIFTS = 3                # number of largest lifts that get post-processing
POST_SLICE = 0.5              # seconds per growth variant on a lift
ILS_STEP = 0.5                # seconds allowed for one remove-and-regrow step
ILS_MAX_N = 2000              # skip iterated search on graphs larger than this (validation cost)

# Semidirect-product group lifts Z_m x|_r Z_k. The dihedral family (k = 2, r = m-1)
# is a special case, so it is covered by this search.
GROUP_S = (1, 2, 3)           # base vertices per side for group lifts
GROUP_ITERS = 150             # annealing iterations per group probe
GROUP_RETRY_ITERS = 500       # annealing iterations per group retry
GROUP_FRAC = 0.4              # fraction of remaining time given to group lifts
MAX_GROUP_K = 8               # largest k in Z_m x|_r Z_k


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cand, sets, target, budget):
    """Pick at most `budget` candidates whose `sets` bitmasks jointly cover `target`.

    Returns the chosen list (possibly empty if target is already covered), or None.
    """
    cand = list(cand)
    covered = 0
    chosen = []
    while (target & ~covered) and len(chosen) < budget and cand:
        best_u, best_gain = -1, 0
        for u in cand:
            g = (sets[u] & target & ~covered).bit_count()
            if g > best_gain:
                best_u, best_gain = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= sets[best_u]
        cand.remove(best_u)
    if target & ~covered:
        return None
    return chosen


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _pair_extend(n, edges, d, D, rng, deadline):
    """Add two adjacent new vertices x (side c) and y (side 1-c) at once.

    x gets neighbours N whose radius-(D-1) balls cover everything. y gets neighbours M
    chosen so that balls_{D-1}(M) covers everything not already within D-2 of N. Old-to-old
    distances only shrink, so the diameter bound is preserved.
    """
    edges = list(edges)
    if D < 3 or n == 0 or d < 2:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        b1 = lib._balls(n, edges, D - 1)
        b2 = lib._balls(n, edges, D - 2)
        placed = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            side_other = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            side_c = [u for u in range(n) if color[u] == c and deg[u] < d]
            N = _greedy_cover(side_other, b1, full, d - 1)
            if not N:
                continue
            b2N = 0
            for u in N:
                b2N |= b2[u]
            M = _greedy_cover(side_c, b1, full & ~b2N, d - 1)
            if M is None:
                continue
            x, y = n, n + 1
            n += 2
            color.append(c)
            color.append(1 - c)
            deg.append(len(N) + 1)
            deg.append(len(M) + 1)
            for u in N:
                edges.append((u, x))
                deg[u] += 1
            for u in M:
                edges.append((u, y))
                deg[u] += 1
            edges.append((x, y))
            placed = True
            break
        if not placed:
            break
    return n, edges


def _grow(n, edges, d, D, rng, deadline):
    """Alternate single-vertex and paired greedy extension until neither adds anything."""
    prev = -1
    while n != prev and time.monotonic() < deadline:
        prev = n
        n, edges = _extend(n, edges, d, D, rng, deadline)
        n, edges = _pair_extend(n, edges, d, D, rng, deadline)
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _growth_variants(g, d, D, rng, end, slice_s):
    """Run both greedy growth styles (single-vertex only, and single+paired) on graph g."""
    out = []
    for fn in (_extend, _grow):
        e = min(end, time.monotonic() + slice_s)
        out.append(fn(g[0], g[1], d, D, rng, e))
    return out


def _best_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    best = _best_valid(cands, d, D)
    if best is not None:
        return best
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- iterated remove-and-regrow

def _remove_vertex(n, edges, v):
    """Return (n-1, edges) with vertex v deleted and the remaining labels compacted."""
    out = []
    for a, b in edges:
        if a == v or b == v:
            continue
        a2 = a - 1 if a > v else a
        b2 = b - 1 if b > v else b
        out.append((a2, b2))
    return n - 1, out


def _ils(n, edges, d, D, rng, end):
    """Iterated local search: delete a random vertex, regrow greedily, keep the result if it
    is valid and at least as large. Returns the largest valid graph seen."""
    cur = (n, list(edges))
    best = cur
    while time.monotonic() < end:
        n0, e0 = cur
        if n0 < 4:
            break
        v = rng.randrange(n0)
        m, e1 = _remove_vertex(n0, e0, v)
        step_end = min(end, time.monotonic() + ILS_STEP)
        m, e2 = _grow(m, e1, d, D, rng, step_end)
        if m >= n0 and lib.is_valid(m, e2, d, D):
            cur = (m, e2)
            if m > best[0]:
                best = (m, e2)
    return best


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

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
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- cyclic lifts (annealing)

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
    """For fixed s, find the largest m (doubling then bisection) whose cyclic lift passes annealing.

    Returns (best, lo, hi): best is (m, P, V) or None, lo the largest m that succeeded
    (0 if none), hi the smallest m above lo that failed (None if not established).
    """
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
    return best, lo, hi


def _retry_cyclic(s, lo, hi, d, D, rng, end, cap):
    """Keep re-annealing at the first size above the best cyclic lift; move up on success."""
    m = hi if hi is not None else lo + 1
    best = None
    while time.monotonic() < end:
        if 2 * s * m > cap:
            break
        st = _anneal(s, m, d, D, rng, end)
        if st is None:
            continue
        g = _graph(s, m, st[0], st[1], d)
        if best is None or g[0] > best[0]:
            best = g
        m += 1
    return best


# ---------------------------------------------------------------- semidirect-product group lifts

def _semi_powers(m, k, r):
    """powers[b] = r^b mod m as an int64 array (for the semidirect product Z_m x|_r Z_k)."""
    return np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)


def _group_mul_vec(X, g, m, k, pw):
    """Vectorised product x * g for an array X of element codes and a scalar code g.

    Element (a, b) is coded a*k + b, and (a, b)(c, d) = (a + r^b c, b + d).
    """
    a1, b1 = X // k, X % k
    c, dd = g // k, g % k
    a = (a1 + pw[b1] * c) % m
    b = (b1 + dd) % k
    return a * k + b


def _group_inv(g, m, k, pw):
    """Scalar inverse of element code g."""
    a, b = divmod(g, k)
    nb = (-b) % k
    return ((-int(pw[nb]) * a) % m) * k + nb


def _group_candidates(lo, hi, rng, limit=60):
    """Groups Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1) with order in [lo, hi].

    Returns (order, m, k, r) tuples sorted by ascending order, ties shuffled.
    k = 2 with r = m - 1 is the dihedral family.
    """
    out = []
    for k in range(1, MAX_GROUP_K + 1):
        found = 0
        for m in range(hi // k, max(1, lo // k) - 1, -1):
            if m < 2:
                break
            if k == 1:
                out.append((m, m, 1, 1))
                found += 1
            else:
                for r in range(1, m):
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                        out.append((m * k, m, k, r))
                        found += 1
                        if found >= limit:
                            break
            if found >= limit:
                break
    rng.shuffle(out)
    out.sort(key=lambda t: t[0])
    return out


def _group_nbr(P, Pinv, G, s, order, m, k, pw):
    """Neighbour table of the group lift: A vertex (i, x) ~ B vertex (P[t,i], x*G[t,i])."""
    d = P.shape[0]
    X = np.arange(order, dtype=np.int64)
    nbr = np.empty((2 * s * order, d), dtype=np.int64)
    for t in range(d):
        for i in range(s):
            j = int(P[t, i])
            g = int(G[t, i])
            nbr[i * order:(i + 1) * order, t] = (s + j) * order + _group_mul_vec(X, g, m, k, pw)
        for j in range(s):
            i = int(Pinv[t, j])
            gi = _group_inv(int(G[t, i]), m, k, pw)
            nbr[(s + j) * order:(s + j + 1) * order, t] = i * order + _group_mul_vec(X, gi, m, k, pw)
    return nbr


def _anneal_group(s, m, k, r, d, D, rng, deadline, iters):
    """Anneal base permutations P and group voltages G for the lift over Z_m x|_r Z_k.

    Left translation by any group element is an automorphism of the lift, so it suffices
    to measure distances from one representative per base vertex.
    """
    order = m * k
    pw = _semi_powers(m, k, r)
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for t in range(d):
        for i in range(s):
            Pinv[t, P[t, i]] = i
    G = np.array([[rng.randrange(order) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * order for i in range(2 * s)]
    nbr = _group_nbr(P, Pinv, G, s, order, m, k, pw)
    cur = _cost(nbr, sources, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if s == 1 or rng.random() < 0.7:
            t, i = rng.randrange(d), rng.randrange(s)
            old = int(G[t, i])
            new_g = rng.randrange(order)
            if new_g == old:
                continue
            G[t, i] = new_g
            cand = _group_nbr(P, Pinv, G, s, order, m, k, pw)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                G[t, i] = old
        else:
            t = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, t, a, b)
            cand = _group_nbr(P, Pinv, G, s, order, m, k, pw)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, t, a, b)
    if cur == 0:
        return P.copy(), G.copy()
    return None


def _group_graph(s, m, k, r, P, G, d):
    """Materialise the group lift with lib.group_lift (deduplicated, bipartite by construction)."""
    darts = []
    for t in range(d):
        for i in range(s):
            darts.append((i, s + int(P[t, i]), int(G[t, i])))
    mul = lib.semidirect_group(m, k, r)[1]
    return lib.group_lift(2 * s, darts, m * k, mul)


def _group_search(d, D, rng, end, cap):
    """Binary-search the largest valid group lift per base size s, within the time budget.

    Returns one record per base size: the pool of candidate groups, the smallest pool
    index that failed (where retries start), and the best valid graph found.
    """
    recs = []
    for idx, s in enumerate(GROUP_S):
        now = time.monotonic()
        if now >= end:
            break
        slice_end = now + (end - now) / (len(GROUP_S) - idx)
        hi_order = cap // (2 * s)
        if hi_order < 2:
            continue
        lo_order = max(2, hi_order // 3)
        pool = _group_candidates(lo_order, hi_order, rng)
        if not pool:
            continue
        rec = {"s": s, "pool": pool, "hi_i": len(pool), "best": None}
        lo_i, hi_i = -1, len(pool)
        while hi_i - lo_i > 1 and time.monotonic() < slice_end:
            mid = (lo_i + hi_i) // 2
            _, m, k, r = pool[mid]
            res = _anneal_group(s, m, k, r, d, D, rng, slice_end, GROUP_ITERS)
            if res is None:
                hi_i = mid
            else:
                lo_i = mid
                n, edges = _group_graph(s, m, k, r, res[0], res[1], d)
                if rec["best"] is None or n > rec["best"][0]:
                    rec["best"] = (n, edges)
        rec["hi_i"] = hi_i
        recs.append(rec)
    return recs


def _retry_group(rec, d, D, rng, end):
    """Re-anneal at the first failing group size; on success move to the next larger candidate."""
    s, pool = rec["s"], rec["pool"]
    idx = rec["hi_i"]
    best = None
    while time.monotonic() < end and idx < len(pool):
        _, m, k, r = pool[idx]
        res = _anneal_group(s, m, k, r, d, D, rng, end, GROUP_RETRY_ITERS)
        if res is None:
            continue
        n, edges = _group_graph(s, m, k, r, res[0], res[1], d)
        if best is None or n > best[0]:
            best = (n, edges)
        idx += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    ils_end = start + max(0.5, ILS_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D >= 3: projective plane (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.extend(_growth_variants(g, d, D, rng,
                                              min(deadline, time.monotonic() + 2 * GROW_SLICE),
                                              GROW_SLICE))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of the remaining time).
    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Semidirect-product group lifts (non-cyclic groups, includes dihedral).
    group_recs = []
    now = time.monotonic()
    if now < deadline:
        group_end = now + GROUP_FRAC * (deadline - now)
        group_recs = _group_search(d, D, rng, group_end, cap)
        for rec in group_recs:
            if rec["best"] is not None:
                cands.append(rec["best"])

    # Cyclic voltage-lift annealing, one slice per base size s.
    lifts = []
    cyc_top = None   # (n, s, lo, hi) for the largest cyclic lift
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        best, lo, hi = _search(s, d, D, rng, slice_end, cap)
        if best is not None:
            m, P, V = best
            g = _graph(s, m, P, V, d)
            cands.append(g)
            lifts.append(g)
            if cyc_top is None or g[0] > cyc_top[0]:
                cyc_top = (g[0], s, lo, hi)

    # Retry annealing just above the largest cyclic lift and the largest group lift.
    grp_top = None
    for rec in group_recs:
        if rec["best"] is not None and (grp_top is None or rec["best"][0] > grp_top["best"][0]):
            grp_top = rec
    retry_stop = deadline + 0.5 * max(0.0, post_end - deadline)
    jobs = []
    if cyc_top is not None:
        jobs.append("cyc")
    if grp_top is not None:
        jobs.append("grp")
    for j, job in enumerate(jobs):
        now = time.monotonic()
        if now >= retry_stop:
            break
        job_end = now + (retry_stop - now) / (len(jobs) - j)
        if job == "cyc":
            _, s, lo, hi = cyc_top
            g = _retry_cyclic(s, lo, hi, d, D, rng, job_end, cap)
        else:
            g = _retry_group(grp_top, d, D, rng, job_end)
        if g is not None:
            cands.append(g)
            lifts.append(g)

    # Post-process the largest lifts: fill spare degree, then grow with both styles.
    lifts.sort(key=lambda g: -g[0])
    for g in lifts[:POST_LIFTS]:
        if time.monotonic() >= post_end:
            break
        aug = _augment(g[0], g[1], d, seed)
        cands.append(aug)
        cands.extend(_growth_variants(aug, d, D, rng, post_end, POST_SLICE))

    # Iterated remove-and-regrow on the best valid graph found so far.
    if D >= 3 and time.monotonic() < ils_end:
        best = _best_valid(cands, d, D)
        if best is not None and best[0] <= ILS_MAX_N:
            cands.append(_ils(best[0], best[1], d, D, rng, ils_end))

    return _finish(cands, d, D)
