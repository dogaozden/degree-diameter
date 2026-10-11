import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Shared helpers
# ----------------------------------------------------------------------------

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


def _ball_cost(n, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff connected with diameter <= D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 1: voltage lifts over semidirect products Z_m x| Z_k, annealed on voltages.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 3, 4, 6])
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


def _lift_cost(k, G, D, darts, perms):
    """Bad-pair count of the lift; duplicate darts are rejected outright."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return _ball_cost(N, adj, D)


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_search(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages of a k-vertex-per-side base with d darts per layer."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        new_s = rng.randrange(G)
        if new_s == old_s:
            continue
        old_pm = perms[idx]
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _lift_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm
    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Family 2 (new): vertex-pair insertion + double-edge-swap annealing.
#
# Given a valid graph, add one A-vertex a and one B-vertex b. Pick d edges
# (x_i, y_i) with distinct endpoints, delete them, and join a to every y_i and
# b to every x_i. All old degrees are preserved and a, b have degree d. Then
# anneal with bipartiteness-preserving double-edge swaps until the graph has
# diameter <= D again. Repeat, growing the graph by two vertices per success.
# ----------------------------------------------------------------------------

def _edge_cost(N, E, D):
    adj = [[] for _ in range(N)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return _ball_cost(N, adj, D)


def _swap_step(n, edges, d, D, rng, deadline):
    """Try to grow a valid graph by one A-vertex and one B-vertex; return (n+2, edges) or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    rng.shuffle(E)

    chosen = []
    used_a, used_b = set(), set()
    for x, y in E:
        if x not in used_a and y not in used_b:
            chosen.append((x, y))
            used_a.add(x)
            used_b.add(y)
            if len(chosen) == d:
                break
    if len(chosen) < d:
        return None

    cs = set(chosen)
    a, b, N = n, n + 1, n + 2
    E = [e for e in E if e not in cs]
    for x, y in chosen:
        E.append((a, y))
        E.append((x, b))

    S = set(E)
    cur = _edge_cost(N, E, D)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[i] = n1
        E[j] = n2
        new = _edge_cost(N, E, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add(n1)
            S.add(n2)
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
        T = max(0.3, T * 0.9995)
    if cur != 0:
        return None
    return N, E


def _swap_grow(n, edges, d, D, rng, deadline):
    """Repeatedly insert vertex pairs while annealing succeeds; stop at the first failure."""
    cur_n, cur_e = n, list(edges)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        budget = now + 0.6 * (deadline - now)
        res = _swap_step(cur_n, cur_e, d, D, rng, budget)
        if res is None:
            break
        cur_n, cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 1: voltage lifts over semidirect products (fast structured base).
    lift_end = start + (0.3 if D >= 3 else 0.5) * time_limit
    ks = [1, 2, 3] if D >= 3 else [1, 2]
    while time.monotonic() < lift_end:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 4))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_search(d, D, k, order, mul, rng, lift_end, 400)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: grow the best graph by vertex-pair insertion with swap annealing.
    if D >= 3 and best[0] >= 2 * d and time.monotonic() < deadline:
        n2, e2 = _swap_grow(best[0], best[1], d, D, rng, deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
