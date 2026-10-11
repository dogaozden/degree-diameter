import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Generic graph utilities on adjacency lists.
# ----------------------------------------------------------------------------

def _adj_from_edges(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _bad_pairs_adj(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask BFS from every vertex)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW: edge-rerouting vertex insertion with annealed repair.
#
# Given a bipartite graph with max degree d, add one new vertex x on side 0 and
# one new vertex y on side 1. Pick d edges (a_i, b_i) with all a_i distinct and
# all b_i distinct, delete them, and join x to every b_i and y to every a_i.
# Every old vertex keeps its degree, x and y get degree d, and the graph stays
# bipartite with max degree d. The diameter is usually broken, so simulated
# annealing over the choice of the d removed edges searches for a choice whose
# result has no bad pairs. Each success adds two vertices and can be repeated.
# ----------------------------------------------------------------------------

def _insert_graph(n, adj, removed):
    """Adjacency lists after rerouting `removed` = [(a, b), ...] through new vertices n (side 0) and n+1 (side 1)."""
    new = [list(a) for a in adj]
    new.append([])
    new.append([])
    x, y = n, n + 1
    for a, b in removed:
        new[a].remove(b)
        new[b].remove(a)
    for a, b in removed:
        new[x].append(b)
        new[b].append(x)
        new[y].append(a)
        new[a].append(y)
    return new


def _grow_once(n, adj, color, d, D, rng, deadline, iters):
    """Try to insert one (side-0, side-1) vertex pair by rerouting d edges. Returns (n+2, adj, color) or None."""
    edges = [(u, v) for u in range(n) if color[u] == 0 for v in adj[u]]
    m = len(edges)
    if m < d:
        return None

    def compatible(e, others):
        a, b = edges[e]
        for c in others:
            ca, cb = edges[c]
            if ca == a or cb == b:
                return False
        return True

    order = list(range(m))
    rng.shuffle(order)
    chosen = []
    for e in order:
        if len(chosen) == d:
            break
        if compatible(e, chosen):
            chosen.append(e)
    if len(chosen) < d:
        return None

    def score(ch):
        new = _insert_graph(n, adj, [edges[c] for c in ch])
        return _bad_pairs_adj(n + 2, new, D), new

    cost, new = score(chosen)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(d)
        others = chosen[:i] + chosen[i + 1:]
        cand = None
        for _ in range(40):
            c = rng.randrange(m)
            if c in chosen:
                continue
            if compatible(c, others):
                cand = c
                break
        if cand is None:
            continue
        trial = others + [cand]
        c2, new2 = score(trial)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            chosen, cost, new = trial, c2, new2
    if cost != 0:
        return None
    return n + 2, new, color + [0, 1]


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
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
    """Simulated annealing over voltages and per-layer B-assignments."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle C_{2D} has diameter D.
        return lib.haar_graph(D, [0, 1])
    # Projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_edges = lib.haar_graph(d, range(d))
    best_n = fb_n
    best_adj = _adj_from_edges(fb_n, fb_edges)
    best_color = _bipartition(fb_n, best_adj)

    deadline = start + 0.85 * time_limit
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]

    while time.monotonic() < deadline:
        # Lift attempt aimed just above the current best order.
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is not None:
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1500)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                n, edges = res
                best_n = n
                best_adj = _adj_from_edges(n, edges)
                best_color = _bipartition(n, best_adj)

        # Repeated growth by edge-rerouting insertion from the best graph.
        fails = 0
        while fails < 2 and time.monotonic() < deadline:
            r = _grow_once(best_n, best_adj, best_color, d, D, rng, deadline, iters=2500)
            if r is None:
                fails += 1
                continue
            best_n, best_adj, best_color = r
            fails = 0

    n = best_n
    edges = [(u, v) for u in range(n) for v in best_adj[u] if u < v]
    if not lib.is_valid(n, edges, d, D):
        return fb_n, fb_edges
    return n, edges
