import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3 and 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# NEW: double-edge-swap annealing after a vertex-pair insertion (diameter 3).
#
# Insertion: pick d pairwise-disjoint edges (a_i, b_i) with a_i in side A and b_i in side B,
# delete them, and add a new A-vertex x joined to every b_i and a new B-vertex y joined to
# every a_i. Degrees stay <= d and the graph grows by 2 vertices.
#
# Repair: double-edge swaps (a,b),(c,e) -> (a,e),(c,b) preserve every degree and the
# bipartition. Simulated annealing on lib.bad_pairs drives the count of distance > D pairs
# to zero.
# ----------------------------------------------------------------------------

def _bipartition(n, edges):
    """Two-colouring of a bipartite graph given by an edge list."""
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


def _insert_pair(n, edges, d, color, rng):
    """Add new vertices x (side 0) and y (side 1) by splitting d disjoint edges; None if impossible."""
    idx = list(range(len(edges)))
    rng.shuffle(idx)
    used = set()
    chosen = []
    for i in idx:
        a, b = edges[i]
        if color[a] == 1:
            a, b = b, a
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        chosen.append((a, b))
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    x, y = n, n + 1
    drop = {(min(a, b), max(a, b)) for a, b in chosen}
    E = [e for e in edges if (min(e), max(e)) not in drop]
    for a, b in chosen:
        E.append((x, b))
        E.append((a, y))
    return n + 2, E, list(color) + [0, 1]


def _anneal_insert(n, E, color, D, rng, deadline):
    """Double-edge-swap annealing on bad_pairs; returns the edge list if it reaches 0, else None."""
    E = [list(e) for e in E]
    for e in E:
        if color[e[0]] == 1:
            e[0], e[1] = e[1], e[0]
    S = {(a, b) for a, b in E}
    m = len(E)
    if m < 2:
        return None
    cost = lib.bad_pairs(n, E, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 1.5 * (0.02 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, f = E[j]
        if a == c or b == f:
            continue
        if (a, f) in S or (c, b) in S:
            continue
        E[i] = [a, f]
        E[j] = [c, b]
        new = lib.bad_pairs(n, E, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            S.discard((a, b))
            S.discard((c, f))
            S.add((a, f))
            S.add((c, b))
            cost = new
        else:
            E[i] = [a, b]
            E[j] = [c, f]
    if cost == 0:
        return [tuple(e) for e in E]
    return None


def _grow_d3(n, edges, d, D, time_end, rng):
    """Repeatedly insert a vertex pair and repair by swaps; returns the largest valid graph reached."""
    while time.monotonic() < time_end:
        color = _bipartition(n, edges)
        ins = _insert_pair(n, edges, d, color, rng)
        if ins is None:
            break
        n2, E2, c2 = ins
        now = time.monotonic()
        budget_end = min(time_end, now + max(4.0, 0.25 * (time_end - now)))
        res = _anneal_insert(n2, E2, c2, D, rng, budget_end)
        if res is not None and lib.is_valid(n2, res, d, D):
            n, edges = n2, res
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (diameter >= 4 fallback).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # NEW: vertex-pair insertion plus swap-annealing repair, from the best base found.
        if time.monotonic() < end:
            n2, e2 = _grow_d3(best_n, best_e, d, D, end, rng)
            consider(n2, e2)

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
