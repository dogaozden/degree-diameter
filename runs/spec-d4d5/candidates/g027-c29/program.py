"""Projective-plane / voltage-lift seeds, grown by a new vertex-pair splitting move.

New in this version: edge-split growth with 2-switch repair. From a d-regular-ish
valid graph, pick d edges (a_i, b_i) with distinct endpoints, add two new vertices
v (side A) and w (side B), and rewire to (v, b_i) and (a_i, w). Degrees stay at
most d and the graph stays bipartite, and the order grows by 2. Degree-preserving
2-switches then anneal the bad-pair count (pairs at distance > D) back to zero.
Failed trials are discarded and the search restarts from the last valid graph.
"""
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Seeds
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
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


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D."""
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
    """Simulated annealing over voltages and per-layer B-assignments for a bi-Cayley lift."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

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
# Edge-split growth with 2-switch repair (new helper).
#
# State: (n, adj, E, color), where adj is a list of sets, E is a list of [a, b]
# with color[a] == 0 and color[b] == 1, and color is the bipartition.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
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


def _state_from(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    E = [[u, v] if color[u] == 0 else [v, u] for u, v in edges]
    return (n, adj, E, color)


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
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


def _split(state, d, rng):
    """Add two vertices v (side A) and w (side B). Remove d edges (a_i, b_i) with distinct
    endpoints and add (v, b_i), (a_i, w). Degrees stay <= d, bipartiteness is kept."""
    n, adj0, E0, color0 = state
    idx = list(range(len(E0)))
    rng.shuffle(idx)
    usedA, usedB, chosen = set(), set(), []
    for i in idx:
        a, b = E0[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    pairs = [E0[i] for i in chosen]
    E2 = [e for i, e in enumerate(E0) if i not in chosen_set]
    adj = [set(s) for s in adj0]
    v, w = n, n + 1
    adj.append(set())
    adj.append(set())
    color = list(color0) + [0, 1]
    for a, b in pairs:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[v].add(b)
        adj[b].add(v)
        adj[w].add(a)
        adj[a].add(w)
        E2.append([v, b])
        E2.append([a, w])
    return (n + 2, adj, E2, color)


def _set_edge(adj, a, b, on):
    if on:
        adj[a].add(b)
        adj[b].add(a)
    else:
        adj[a].discard(b)
        adj[b].discard(a)


def _repair(state, D, rng, deadline, iters, T):
    """Anneal degree-preserving 2-switches to drive the bad-pair count to zero."""
    n, adj, E, _ = state
    m = len(E)
    cost = _bad(n, adj, D)
    if m < 2:
        return cost == 0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _set_edge(adj, a1, b1, False)
        _set_edge(adj, a2, b2, False)
        _set_edge(adj, a1, b2, True)
        _set_edge(adj, a2, b1, True)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            _set_edge(adj, a1, b2, False)
            _set_edge(adj, a2, b1, False)
            _set_edge(adj, a1, b1, True)
            _set_edge(adj, a2, b2, True)
    return cost == 0


def _grow(state, d, D, moore, deadline, rng, consider, iters, T):
    """Repeatedly split-insert and repair; keep each success as the new base."""
    cur = state
    while time.monotonic() < deadline:
        trial = _split(cur, d, rng)
        if trial is None or trial[0] > moore:
            break
        if _repair(trial, D, rng, deadline, iters, T):
            cur = trial
            n = cur[0]
            consider(n, [(a, b) for a, b in cur[2]])
    return cur


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    moore = lib._moore_bound(d, D)
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
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

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= moore or D < 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Phase 1: annealed voltage lifts (seeds for the growth phase).
    lift_deadline = start + 0.45 * (deadline - start)
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    anneal_iters = 1500 if D >= 5 else 400
    while time.monotonic() < lift_deadline:
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
        res = _anneal(d, D, k, order, mul, rng, lift_deadline, anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: edge-split growth with 2-switch repair from the best valid graph.
    if time.monotonic() < deadline:
        state = _state_from(best[0], best[1])
        _grow(state, d, D, moore, deadline, rng, consider,
              iters=2000, T=0.5)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
