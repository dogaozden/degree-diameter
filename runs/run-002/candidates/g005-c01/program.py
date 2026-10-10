import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 3000                  # annealing iterations per group probe
S_GROUP = (1, 2, 3, 4, 5, 6)  # base vertices per side for group lifts
GMAX = 1200                   # largest group order considered
K_MAX = 6                     # largest k in Z_m x|_r Z_k
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
GROW_SLICE = 0.5              # seconds per greedy growth variant (base graphs)
POST_SLICE = 0.5              # seconds per growth variant on a lift
POST_LIFTS = 3                # number of largest lifts that get post-processing
ILS_STEP = 0.5                # seconds allowed for one remove-and-regrow step
HAAR_ITERS = 120              # hill-climb steps per Haar modulus


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
    chosen so that balls_{D-1}(M) covers everything not already within D-2 of N.
    Old-to-old distances only shrink, so the diameter bound is preserved.
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

    Extra edges only shorten distances and keep the graph bipartite.
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


# ---------------------------------------------------------------- group lifts (annealing)

def _group_tables(key):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a, b) coded as a*k+b.

    key = (m, k, r) with r^k = 1 mod m and gcd(r, m) = 1. The cyclic group Z_G is (G, 1, 1).
    Returns (G, T, inv) with T[x, y] = x*y and inv[x] = x^{-1}; identity is index 0.
    """
    m, k, r = key
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, e, m) for e in range(k)], dtype=np.int64)
    # (a, b) * (c, d) = (a + r^b c, b + d)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    # (a, b)^{-1} = (-r^{-b} a, -b)
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return G, T, inv


def _neighbors(P, Pinv, V, s, G, T, inv):
    """Neighbour table (2sG x d) of the group lift of a d-regular bipartite base on s+s vertices.

    Dart k joins A-vertex (i, x) to B-vertex (P[k, i], x*g) with g = V[k, i].
    A-lift id = i*G + x, B-lift id = (s+j)*G + y.
    """
    d = P.shape[0]
    nbr = np.empty((2 * s * G, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            g = int(V[k, i])
            nbr[i * G:(i + 1) * G, k] = s * G + int(P[k, i]) * G + T[:, g]
        for j in range(s):
            i = int(Pinv[k, j])
            g = int(V[k, i])
            nbr[(s + j) * G:(s + j + 1) * G, k] = i * G + T[:, inv[g]]
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid.

    Left multiplication by the group is an automorphism transitive on each fibre,
    so checking the identity of each base fibre suffices.
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


def _anneal(s, G, T, inv, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(G) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * G for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, G, T, inv)
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
            cand = _neighbors(P, Pinv, V, s, G, T, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, G, T, inv)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, key, P, V, d):
    """Materialise the group lift as (n, edges), deduplicated (A-side enumeration gives each edge once)."""
    G, T, inv = _group_tables(key)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, G, T, inv)
    edges = set()
    for x in range(s * G):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * G, sorted(edges)


def _candidate_keys(gmax):
    """Map each order G in 2..gmax to its candidate groups: the cyclic group first, then semidirect ones."""
    cands = {G: [(G, 1, 1)] for G in range(2, gmax + 1)}
    for k in range(2, K_MAX + 1):
        for m in range(2, gmax // k + 1):
            G = m * k
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands[G].append((m, k, r))
    return cands


def _search_groups(s, d, D, rng, deadline, orders, cands):
    """Bisection over the sorted group orders for the largest G whose lift passes annealing.

    For each order, a few candidate groups are tried (cyclic first, then random semidirect ones).
    """
    best = None
    lo, hi = -1, len(orders)
    while lo + 1 < hi and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        G = orders[mid]
        keys = cands[G]
        nonab = list(keys[1:])
        rng.shuffle(nonab)
        tries = [keys[0]] + nonab[:2]
        found = None
        for key in tries:
            now = time.monotonic()
            if now >= deadline:
                break
            budget_end = min(deadline, now + max(0.2, 0.35 * (deadline - now)))
            _, T, inv = _group_tables(key)
            st = _anneal(s, G, T, inv, d, D, rng, budget_end)
            if st is not None:
                found = (key, st[0], st[1])
                break
        if found is not None:
            lo = mid
            best = (G, found[0], found[1], found[2])
        else:
            hi = mid
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.65 * time_limit - 1.0)     # constructions and lift search
    post_end = start + max(0.5, 0.75 * time_limit - 1.0)     # post-processing of lifts
    ils_end = start + max(0.5, 0.85 * time_limit - 1.0)      # iterated local search
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
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and lib.is_prime_power(d - 1) and d - 1 <= GQ_Q_MAX:
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
        S = _search_haar(d, D, haar_m, rng, haar_end, HAAR_ITERS)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Group lifts over cyclic and semidirect groups, one bisection per base size s.
    group_lifts = []
    gmax = min(GMAX, cap // 2)
    if gmax >= 2 and time.monotonic() < deadline:
        keys = _candidate_keys(gmax)
        orders = sorted(keys)
        for idx, s in enumerate(S_GROUP):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_end = now + (deadline - now) / (len(S_GROUP) - idx)
            gs = cap // (2 * s)
            ords = [G for G in orders if G <= gs]
            if not ords:
                continue
            res = _search_groups(s, d, D, rng, slice_end, ords, keys)
            if res is not None:
                G, key, P, V = res
                g = _graph(s, key, P, V, d)
                if lib.is_valid(g[0], g[1], d, D):
                    group_lifts.append(g)
                    cands.append(g)

    # Post-process the largest lifts: fill spare degree, then grow with both styles.
    group_lifts.sort(key=lambda g: -g[0])
    for g in group_lifts[:POST_LIFTS]:
        if time.monotonic() >= post_end:
            break
        aug = _augment(g[0], g[1], d, seed)
        cands.append(aug)
        cands.extend(_growth_variants(aug, d, D, rng, post_end, POST_SLICE))

    # Iterated remove-and-regrow on the largest valid graph found so far.
    if time.monotonic() < ils_end:
        best = _best_valid(cands, d, D)
        if best is not None:
            cands.append(_ils(best[0], best[1], d, D, rng, ils_end))

    return _finish(cands, d, D)
