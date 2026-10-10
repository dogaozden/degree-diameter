import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New helper: spare-degree greedy augmentation.
#
# Many structured graphs (projective planes with d-1 not a prime power, for
# instance) have a few vertices of degree below d. The routine below grows such
# a graph by random bipartite attachments: it adds a new vertex on one side
# joined to a random set of spare vertices on the other side, or adds a single
# edge between two spare vertices on opposite sides. Every move is kept only if
# the whole graph remains valid (degree <= d, bipartite, diameter <= D), so the
# output is always valid.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Return a proper 2-colouring as a list, or None if the graph is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _augment(n, edges, d, D, rng, deadline):
    """Greedily add vertices and edges using spare degree while keeping the graph valid."""
    E = set((min(u, v), max(u, v)) for u, v in edges)
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    if color is None:
        return n, sorted(E)
    cur_n = n
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        spare = [[v for v in range(cur_n) if color[v] == s and len(adj[v]) < d]
                 for s in (0, 1)]
        if not spare[0] and not spare[1]:
            break
        if rng.random() < 0.6:
            # Add a new vertex on side s, joined to random spare vertices of side 1-s.
            s = rng.randrange(2)
            pool = spare[1 - s]
            if not pool:
                fails += 1
                continue
            k = rng.randint(1, min(d, len(pool)))
            chosen = rng.sample(pool, k)
            new = cur_n
            newE = [(min(new, c), max(new, c)) for c in chosen]
            if lib.is_valid(cur_n + 1, list(E) + newE, d, D):
                E.update(newE)
                adj.append(set(chosen))
                for c in chosen:
                    adj[c].add(new)
                color.append(s)
                cur_n += 1
                fails = 0
            else:
                fails += 1
        else:
            # Add one edge between spare vertices on opposite sides.
            if not spare[0] or not spare[1]:
                fails += 1
                continue
            a = rng.choice(spare[0])
            b = rng.choice(spare[1])
            if b in adj[a]:
                fails += 1
                continue
            e = (min(a, b), max(a, b))
            if lib.is_valid(cur_n, list(E) + [e], d, D):
                E.add(e)
                adj[a].add(b)
                adj[b].add(a)
                fails = 0
            else:
                fails += 1
    return cur_n, sorted(E)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent's search).
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs plus duplicate-dart penalties. Zero means valid."""
    seen = set()
    dup = 0
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            dup += 1
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen_v = [False] * N
        seen_v[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_v[v]:
                        seen_v[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total + _PENALTY * dup


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages of a base with k vertices per side."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_pm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _cost(k, G, D, darts, perms)
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
            # Spare-degree augmentation on the projective plane (short time slice).
            aug_deadline = start + 0.25 * budget
            if time.monotonic() < aug_deadline:
                an, ae = _augment(pg[0], pg[1], d, D, rng, aug_deadline)
                consider(an, ae)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley lifts over semidirect products.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _search(d, D, k, order, mul, rng, deadline, 500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
