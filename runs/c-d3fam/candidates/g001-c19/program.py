import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
TIME_FRAC = 0.8               # fraction of time_limit used for search
POST_FRAC = 0.85              # fraction of time_limit after which nothing new starts
POST_EXTEND_SLICE = 1.5       # seconds given to greedy extension of the best lift
GROW_REPAIR_STEPS = 150       # repair moves per grow attempt (D = 3 route)
GROW_TEMP = 0.6               # annealing temperature for repair moves


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


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : record constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _araujo_base(d):
    """Araujo-Pardo & Lopez graph for d = q+2 (q a prime power >= 3): order 2(q^2+q+5), diameter 3.

    This is the published record for d-1 not a prime power. It is degree d throughout,
    so it has no spare degree of its own; it is used as the start point for grow-repair.
    """
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


# ---------------------------------------------------------------- D = 3 : grow-and-repair

def _side_state(n, edges, col):
    """Edge set normalised as (side-0 vertex, side-1 vertex), plus degree list."""
    E = set()
    for u, v in edges:
        E.add((u, v) if col[u] == 0 else (v, u))
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    return E, deg


def _cost(n, E, D):
    """Number of vertex pairs at distance > D. Zero iff the graph has diameter <= D."""
    return lib.bad_pairs(n, list(E), D)


def _fill(n, E, col, deg, d, rng):
    """Add side0-side1 edges between non-adjacent vertices that still have spare degree.

    Adding edges only shortens distances, so the cost never increases.
    """
    side0 = [u for u in range(n) if col[u] == 0 and deg[u] < d]
    side1 = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    rng.shuffle(side0)
    rng.shuffle(side1)
    for a in side0:
        for b in side1:
            if deg[a] >= d:
                break
            if deg[b] < d and (a, b) not in E:
                E.add((a, b))
                deg[a] += 1
                deg[b] += 1


def _insert(n, E, col, deg, d, rng):
    """Add a new vertex x (random side c) joined to d random vertices of the other side.

    A chosen neighbour already at full degree gives up one incident edge. That freed
    vertex is repaired later by _fill and the swap moves. Returns the new vertex count.
    """
    c = rng.randrange(2)
    other = [v for v in range(n) if col[v] == 1 - c]
    W = rng.sample(other, d)
    x = n
    n += 1
    col.append(c)
    deg.append(0)
    for w in W:
        if deg[w] >= d:
            e = rng.choice([e for e in E if w in e])
            E.remove(e)
            z = e[0] if e[1] == w else e[1]
            deg[z] -= 1
            deg[w] -= 1
        E.add((x, w) if c == 0 else (w, x))
        deg[w] += 1
        deg[x] += 1
    return n


def _swap_move(E, rng):
    """Propose a degree-preserving double edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)."""
    if len(E) < 2:
        return None
    (a1, b1), (a2, b2) = rng.sample(list(E), 2)
    if a1 == a2 or b1 == b2:
        return None
    if (a1, b2) in E or (a2, b1) in E:
        return None
    return (a1, b1), (a2, b2), (a1, b2), (a2, b1)


def _repair(n, E, col, deg, d, D, rng, steps, deadline):
    """Reduce the diameter defect by filling spare degree and annealing double edge swaps."""
    c = _cost(n, E, D)
    for _ in range(steps):
        if c == 0 or time.monotonic() > deadline:
            break
        _fill(n, E, col, deg, d, rng)
        c = _cost(n, E, D)
        if c == 0:
            break
        mv = _swap_move(E, rng)
        if mv is None:
            continue
        o1, o2, n1, n2 = mv
        E.remove(o1)
        E.remove(o2)
        E.add(n1)
        E.add(n2)
        c2 = _cost(n, E, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / GROW_TEMP):
            c = c2
        else:
            E.remove(n1)
            E.remove(n2)
            E.add(o1)
            E.add(o2)
    return c


def _grow_repair(n, edges, col, d, D, rng, deadline):
    """Iterated grow-and-repair from a valid graph. Returns the largest valid (n, edges) found.

    Each round inserts one vertex, then tries to repair the diameter. A success keeps the
    bigger graph. A failure restores the previous valid graph.
    """
    col = list(col)
    E, deg = _side_state(n, edges, col)
    if _cost(n, E, D) != 0:
        return None
    best = (n, sorted(E))
    while time.monotonic() < deadline:
        sn, sE, scol, sdeg = n, set(E), list(col), list(deg)
        n2 = _insert(n, E, col, deg, d, rng)
        _fill(n2, E, col, deg, d, rng)
        c = _repair(n2, E, col, deg, d, D, rng, GROW_REPAIR_STEPS, deadline)
        if c == 0:
            n = n2
            best = (n2, sorted(E))
        else:
            n, E, col, deg = sn, sE, scol, sdeg
    return best


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


def _cost_lift(nbr, sources, D):
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
    cur = _cost_lift(nbr, sources, D)
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
            c = _cost_lift(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost_lift(cand, sources, D)
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
    """For fixed s, find the largest m (doubling then bisection) whose lift passes annealing."""
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


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D = 3 route: Moore-extremal plane, else record construction + grow-and-repair.
    if D == 3 and d >= 4:
        base = _pg_base(d)
        if base is not None and lib.is_prime_power(d - 1):
            return _finish([base], d, D)     # Moore-extremal, nothing to improve
        if base is not None:
            cands.append(base)
        ara = _araujo_base(d)
        if ara is not None:
            cands.append(ara)
        # Start the growth from the best valid base we have (record first).
        start_g = None
        for g in (ara, base):
            if g is not None and lib.is_valid(g[0], g[1], d, D):
                start_g = g
                break
        if start_g is not None:
            col = _two_colour(start_g[0], start_g[1])
            res = _grow_repair(start_g[0], start_g[1], col, d, D, rng, deadline)
            if res is not None:
                cands.append(res)
        return _finish(cands, d, D)

    # D = 3 with d = 3 and other small cases, and D >= 4: projective plane / GQ + extension.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

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

    # Voltage-lift annealing, one slice per base size s.
    lift_best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            cands.append(g)
            if lift_best is None or g[0] > lift_best[0]:
                lift_best = g

    # Post-process the largest lift: fill spare degree by augmentation, then extend.
    if lift_best is not None and time.monotonic() < post_end:
        aug = _augment(lift_best[0], lift_best[1], d, seed)
        cands.append(aug)
        ext_end = min(post_end, time.monotonic() + POST_EXTEND_SLICE)
        cands.append(_extend(aug[0], aug[1], d, D, rng, ext_end))

    return _finish(cands, d, D)
