import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Generic graph utilities.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    """Adjacency lists for an undirected edge list on vertices 0..n-1."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Proper two-colouring of a bipartite graph given by adjacency lists."""
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (distances only shrink)."""
    out = list(edges)
    adj = _adj_lists(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


# ----------------------------------------------------------------------------
# Base family: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

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
            c2 = _lift_cost(k, G, D, darts, perms)
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
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: bipartite split-growth plus switch-based diameter repair.
#
# split_grow adds one A-vertex x and one B-vertex y by "splitting" d edges
# (a,b): the edge is replaced by (a,y) and (b,x). All old degrees are kept,
# and x, y reach degree d. The result has n+2 vertices, max degree d,
# and is still bipartite, but its diameter is generally too large.
#
# switch_anneal then repairs the diameter with degree-preserving bipartite
# double-edge swaps: (a,b),(c,e) -> (a,e),(c,b). The cost is the number of
# vertex pairs at distance > D, counted with bitmask ball expansion. The
# temperature cools with wall-clock time.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _split_grow(n, edges, color, d, rng):
    """Add one A-vertex and one B-vertex by splitting d edges; returns (n+2, edges, color) or None."""
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]  # (A-end, B-end)
    x, y = n, n + 1  # x on side 0, y on side 1
    col = list(color) + [0, 1]
    used_a, used_b = set(), set()
    for _ in range(d):
        cands = [k for k, (a, b) in enumerate(E) if a not in used_a and b not in used_b]
        if not cands:
            return None
        k = rng.choice(cands)
        a, b = E[k]
        E[k] = (a, y)
        E.append((b, x))
        used_a.add(a)
        used_b.add(b)
    return n + 2, E, col


def _switch_anneal(n, edges, color, D, rng, t_end, T0, T1):
    """Degree-preserving bipartite switch annealing; returns edges with diameter <= D, or None."""
    E = [[a, b] if color[a] == 0 else [b, a] for a, b in edges]
    adj = _adj_lists(n, edges)
    existing = {(min(a, b), max(a, b)) for a, b in edges}
    cost = _bad_count(n, adj, D)
    m = len(E)
    if cost == 0:
        return [(a, b) for a, b in E]

    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while m >= 2:
        now = time.monotonic()
        if now >= t_end or cost == 0:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        k1 = (min(a, e), max(a, e))
        k2 = (min(c, b), max(c, b))
        if k1 in existing or k2 in existing:
            continue
        adj[a].remove(b)
        adj[b].remove(a)
        adj[c].remove(e)
        adj[e].remove(c)
        adj[a].append(e)
        adj[e].append(a)
        adj[c].append(b)
        adj[b].append(c)
        c2 = _bad_count(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            existing.discard((min(a, b), max(a, b)))
            existing.discard((min(c, e), max(c, e)))
            existing.add(k1)
            existing.add(k2)
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            adj[a].remove(e)
            adj[e].remove(a)
            adj[c].remove(b)
            adj[b].remove(c)
            adj[a].append(b)
            adj[b].append(a)
            adj[c].append(e)
            adj[e].append(c)

    if cost == 0:
        return [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Main construction.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    bound = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Early exit: the Moore bound is attained (e.g. PG(2,2) for d=3, D=3).
    if best_n >= bound:
        return best

    # Phase 1: annealed group voltage lifts (this produced the current base).
    lift_end = start + 0.4 * time_limit
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
    else:
        ks = [1, 1, 2, 3]
        anneal_iters = 400
    while time.monotonic() < lift_end:
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
        res = _anneal_lift(d, D, k, order, mul, rng, lift_end, anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: split-growth from the best valid graph, then switch-based diameter repair.
    switch_end = start + 0.85 * time_limit
    slice_len = max(2.0, 0.12 * time_limit)
    while time.monotonic() < switch_end - 0.5:
        base_n, base_e = best
        base_e = _saturate_edges(base_n, base_e, d, rng)
        base_col = _bipartition(base_n, _adj_lists(base_n, base_e))
        g = _split_grow(base_n, base_e, base_col, d, rng)
        if g is None:
            break
        n2, e2, col2 = g
        t_end = min(switch_end, time.monotonic() + slice_len)
        res = _switch_anneal(n2, e2, col2, D, rng, t_end, 2.0, 0.15)
        if res is not None:
            consider(n2, res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
