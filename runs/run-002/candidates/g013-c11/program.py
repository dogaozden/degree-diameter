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
# Group voltage-lift annealing (baseline search).
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (n, edges) with diameter <= D, or None.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Bold change: grow a valid graph by two vertices at a time and repair it by
# local search over edge moves (rewire / swap / fill), minimising the number
# of vertex pairs at distance > D. Adding edges never increases that count, so
# fills are always accepted. Every accepted state has max degree <= d and is
# bipartite by construction; the final graph is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _bad(N, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _side_colors(n, adj):
    """Proper 2-colouring of a bipartite graph given as adjacency sets."""
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


def _grow_one(n, old_adj, d, D, step_deadline, rng):
    """Add one A-vertex and one B-vertex, then repair. Return (N, adj) on success, else None."""
    color = _side_colors(n, old_adj)
    N = n + 2
    adj = [set(s) for s in old_adj] + [set(), set()]
    side = color + [0, 1]
    sides_lists = [[v for v in range(N) if side[v] == s] for s in (0, 1)]

    def deficits():
        return [[v for v in sides_lists[s] if len(adj[v]) < d] for s in (0, 1)]

    def fill():
        added = False
        defs = deficits()
        for x in defs[0]:
            for y in defs[1]:
                if len(adj[x]) >= d:
                    break
                if len(adj[y]) < d and y not in adj[x]:
                    adj[x].add(y)
                    adj[y].add(x)
                    added = True
        return added

    fill()
    cur = _bad(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-9, step_deadline - t0)

    while cur > 0 and time.monotonic() < step_deadline:
        now = time.monotonic()
        frac = min(1.0, (now - t0) / span)
        T = max(0.1, 1.5 * (1.0 - frac) + 0.1)

        if fill():
            cur = _bad(N, adj, D)
            if cur == 0:
                break

        defs = deficits()
        r = rng.random()
        rem = []
        add = []
        if r < 0.7:
            # Rewire: move one endpoint of an edge onto a vertex with spare degree.
            u = rng.randrange(N)
            if not adj[u]:
                continue
            v = rng.choice(list(adj[u]))
            if rng.random() < 0.5:
                mover, keep = u, v
            else:
                mover, keep = v, u
            cands = [x for x in defs[side[mover]] if x != mover and keep not in adj[x]]
            if not cands:
                continue
            x = rng.choice(cands)
            rem = [(mover, keep)]
            add = [(x, keep)]
        else:
            # Swap: two edges (a1,b1), (a2,b2) become (a1,b2), (a2,b1). Degrees unchanged.
            a1 = rng.randrange(N)
            if not adj[a1]:
                continue
            b1 = rng.choice(list(adj[a1]))
            a2 = rng.choice(sides_lists[side[a1]])
            if a2 == a1 or not adj[a2]:
                continue
            b2 = rng.choice(list(adj[a2]))
            if b2 == b1 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            rem = [(a1, b1), (a2, b2)]
            add = [(a1, b2), (a2, b1)]

        for p, q in rem:
            adj[p].discard(q)
            adj[q].discard(p)
        for p, q in add:
            adj[p].add(q)
            adj[q].add(p)

        c2 = _bad(N, adj, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            for p, q in add:
                adj[p].discard(q)
                adj[q].discard(p)
            for p, q in rem:
                adj[p].add(q)
                adj[q].add(p)

    if cur == 0:
        return N, adj
    return None


def _repair(n, edges, d, D, deadline, rng):
    """Repeatedly grow by two vertices while repair succeeds. Return the largest valid (n, edges) found, or None."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    best = None
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        step_dl = min(deadline, now + max(1.5, 0.4 * remaining))
        res = _grow_one(n, adj, d, D, step_dl, rng)
        if res is None:
            break
        N, new_adj = res
        cand_edges = [(u, v) for u in range(N) for v in new_adj[u] if u < v]
        if not lib.is_valid(N, cand_edges, d, D):
            break
        n, adj = N, new_adj
        best = (N, cand_edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < start + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Baseline: annealed group voltage lifts (uses the first portion of the budget).
    anneal_deadline = start + 0.35 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < anneal_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, anneal_deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Different construction: grow-and-repair from the best valid graph found so far.
    if D >= 3 and time.monotonic() < start + 0.7 * time_limit:
        try:
            res = _repair(best_n, best[1], d, D, start + 0.72 * time_limit, rng)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best = res
                best_n = res[0]
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
