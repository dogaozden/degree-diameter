import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline bases: PG(2,q) for D = 3, generalized quadrangle W(q) for D >= 4.
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _bip(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _augment(n, edges, d, rng):
    """Greedily add cross edges between spare-degree vertices. Distances never grow."""
    edges = list(edges)
    deg = [0] * n
    es = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        es.add((min(u, v), max(u, v)))
    color = _bip(n, edges)
    A = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    B = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    rng.shuffle(A)
    for a in A:
        if deg[a] >= d:
            continue
        rng.shuffle(B)
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] < d and (min(a, b), max(a, b)) not in es:
                edges.append((a, b))
                es.add((min(a, b), max(a, b)))
                deg[a] += 1
                deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k.
#
# Vertices: left (i, g) and right (k + j, h), with i, j in [k], g, h in G.
# A dart (i, j, s) joins (i, g) to (k + j, g*s) for every g. Each layer of
# the base is a perfect matching between left and right orbits, so the lift
# is d-regular and bipartite. Left multiplication by x in G is an automorphism,
# so BFS from the 2k orbit representatives (i, identity) gives the exact cost.
# ----------------------------------------------------------------------------

BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
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


def _cost(k, G, D, darts, row, limit):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        r = row(s)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + r[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
        if total > limit:
            return total
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over darts (layer permutations and voltages)."""
    cache = {}

    def row(s):
        r = cache.get(s)
        if r is None:
            r = [mul(g, s) for g in range(G)]
            cache[s] = r
        return r

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, row, BIG)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.03 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, row, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, row, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost != 0:
        return None
    edges = set()
    for i, j, s in darts:
        r = row(s)
        for g in range(G):
            edges.add((i * G + g, (k + j) * G + r[g]))
    return 2 * k * G, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(1.0, 0.80 * T - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]

    # Baselines.
    if D >= 3 and qs:
        consider(*lib.projective_plane_incidence(qs[0]))
    if D >= 4:
        gq = [q for q in qs if q <= 9]
        if gq:
            n0, e0 = _gq_w(gq[0])
            consider(n0, e0)
            consider(n0, _augment(n0, e0, d, rng))

    # Main construction: annealed bi-Cayley lifts with 1..6 orbits per side.
    if d >= 2 and D >= 3:
        ks = [1, 2, 2, 3, 3, 4, 5, 6]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            G0 = best[0] // (2 * k) + 1
            G = G0 + rng.randrange(0, max(2, G0 // 25))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            slice_end = min(deadline, time.monotonic() + max(2.0, 0.12 * T))
            res = _anneal(d, D, k, order, mul, rng, slice_end, iters=4000)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
