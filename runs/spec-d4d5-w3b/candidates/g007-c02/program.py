import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Fixed bases (safe fallbacks): projective plane and generalized quadrangle.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _base_candidates(d, D):
    """Known structured graphs with max degree d, diameter <= D (validated by the caller)."""
    out = []
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    if D >= 3 and qs:
        out.append(lib.projective_plane_incidence(qs[0]))
    if D >= 4 and qs and qs[0] <= 5:
        out.append(_gq_w(qs[0]))
    return out


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover extension, then edge saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g - 1 if (randomize and rng.random() < 0.5) else best_g
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g.
# Each layer L of d darts uses a permutation p_L of the k layers, so every
# vertex has degree exactly d. Left multiplication is an automorphism, so the
# distance check only needs one representative per (side, layer).
#
# Cost is evaluated with numpy: reach sets are updated by a boolean-like matrix
# product, which is much faster than Python BFS for a few hundred vertices.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 6])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _mul_table(G, mul):
    return np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)


def _cost(k, G, D, darts, M):
    """Unreached (representative, vertex) pairs, plus a heavy penalty for duplicate darts."""
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    seen = set()
    pen = 0
    ar = np.arange(G)
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            pen += 1
        seen.add(key)
        pm = M[:, s]
        a = i * G + ar
        b = (k + j) * G + pm
        A[a, b] = 1.0
        A[b, a] = 1.0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = np.zeros((len(reps), N), dtype=np.float32)
    R[np.arange(len(reps)), reps] = 1.0
    for _ in range(D):
        R = np.minimum(R + R @ A, 1.0)
    unreached = len(reps) * N - int(np.count_nonzero(R))
    return unreached + pen * N * N


def _edges(k, G, darts, M):
    E = set()
    for i, j, s in darts:
        pm = M[:, s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(pm[g])))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, M, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, M)
    T0, T_end = 6.0, 0.3
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / iters)
        if rng.random() < 0.75 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, M)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, M)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, M)
    return None


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    for n, e in _base_candidates(d, D):
        consider(n, e)

    # Voltage-lift search: aim for orders just above the current best.
    ks = [1, 1, 2, 2, 3, 4, 5, 6]
    iters = 2500
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        half = best_n // 2 + 1
        extra = rng.randrange(0, 4)
        G = max(2, (half + extra + k - 1) // k)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        M = _mul_table(order, mul)
        res = _anneal(d, D, k, order, M, rng, deadline, iters)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            best_n = res[0]

    # Grow the best graph with diameter-preserving cover extension.
    gn, ge = _grow(best[0], best[1], d, D, start + 0.92 * time_limit, rng)
    consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
