import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Phase 1: annealed bi-Cayley voltage lifts over Z_m x| Z_k (seed generator).
# ----------------------------------------------------------------------------

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


def _cost_lift(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


def _edges_lift(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_lift(k, G, D, darts, perms)
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
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_lift(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Phase 2 (bold): direct annealing on bipartite graphs with vertex growth.
#
# State: edges E as (A-vertex, B-vertex) pairs, with degrees preserved by
# 2-switches. Cost = number of unordered pairs at distance > D. When the cost
# hits zero, the graph is recorded and grown by one A and one B vertex, each of
# degree d, built by splitting d edges with distinct endpoints.
# ----------------------------------------------------------------------------

def _orient(n, edges):
    """Two-colouring of the graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _bad_count(n, adj, D):
    """Unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _switch(E, S, adj, i, j):
    """2-switch: (x,y),(z,w) -> (x,w),(z,y). Calling it twice restores the original."""
    x, y = E[i]
    z, w = E[j]
    S.discard((x, y))
    S.discard((z, w))
    adj[x].discard(y)
    adj[y].discard(x)
    adj[z].discard(w)
    adj[w].discard(z)
    E[i] = [x, w]
    E[j] = [z, y]
    S.add((x, w))
    S.add((z, y))
    adj[x].add(w)
    adj[w].add(x)
    adj[z].add(y)
    adj[y].add(z)


def _grow(n, d, E, S, adj, rng):
    """Add vertices x (side A) and y (side B), each of degree d, by splitting d edges.

    Each chosen edge (a,b) becomes (a,y) and (x,b). Returns the new vertex count,
    or None if d edges with pairwise distinct endpoints cannot be found.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    picks = []
    used_a, used_b = set(), set()
    for idx in order:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        picks.append(idx)
        used_a.add(a)
        used_b.add(b)
        if len(picks) == d:
            break
    if len(picks) < d:
        return None
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    for idx in picks:
        a, b = E[idx]
        S.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
        E[idx] = [a, y]
        S.add((a, y))
        adj[a].add(y)
        adj[y].add(a)
        E.append([x, b])
        S.add((x, b))
        adj[x].add(b)
        adj[b].add(x)
    return n + 2


def _graph_sa(d, D, n, edges, col, deadline, rng, consider):
    adj = [set() for _ in range(n)]
    E = []
    S = set()
    for u, v in edges:
        a, b = (u, v) if col[u] == 0 else (v, u)
        E.append([a, b])
        S.add((a, b))
        adj[a].add(b)
        adj[b].add(a)

    cur = _bad_count(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while time.monotonic() < deadline:
        if cur == 0:
            consider(n, [(a, b) for a, b in E])
            new_n = _grow(n, d, E, S, adj, rng)
            if new_n is None:
                break
            n = new_n
            cur = _bad_count(n, adj, D)
            continue

        m = len(E)
        if m < 2:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x, y = E[i]
        z, w = E[j]
        if x == z or y == w or (x, w) in S or (z, y) in S:
            continue

        _switch(E, S, adj, i, j)
        new = _bad_count(n, adj, D)
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 0.4 * (0.1 ** frac)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _switch(E, S, adj, i, j)


# ----------------------------------------------------------------------------
# Projective plane baseline.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    phase1_end = start + 0.35 * total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 1: voltage-lift seeds.
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    iters = 1500 if D >= 5 else 400
    while time.monotonic() < phase1_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, phase1_end, iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: direct graph annealing with vertex growth, from the best graph so far.
    col = _orient(best[0], best[1])
    if col is not None and time.monotonic() < deadline:
        _graph_sa(d, D, best[0], best[1], col, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
