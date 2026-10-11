import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Voltage lifts of the projective-plane incidence graph PG(2, q) over small
# groups. The base is (q+1)-regular and bipartite with diameter 3. Each base
# edge gets a group voltage, and the lift has N0 * |G| vertices with degree
# q+1 = d. Voltages on a spanning tree are fixed to the identity, which is
# gauge-equivalent. Annealing searches the remaining voltages for diameter <= D.
# ----------------------------------------------------------------------------


def _bad_pairs_bits(N, adj, D):
    """Number of ordered (vertex, unreached vertex) pairs at distance > D. Zero iff diameter <= D."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(N - b.bit_count() for b in ball)


def _tree_edges(N0, base_edges):
    """Indices of the edges of a BFS spanning tree of the base graph."""
    adj = [[] for _ in range(N0)]
    for idx, (u, v) in enumerate(base_edges):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * N0
    seen[0] = True
    stack = [0]
    tree = set()
    while stack:
        u = stack.pop()
        for v, idx in adj[u]:
            if not seen[v]:
                seen[v] = True
                tree.add(idx)
                stack.append(v)
    return tree


def _lift_adj(N0, base_edges, G, T, volt):
    """Adjacency lists of the lift. Dart (u, v) with voltage s joins (u, x) to (v, x*s)."""
    adj = [[] for _ in range(N0 * G)]
    for idx, (u, v) in enumerate(base_edges):
        s = volt[idx]
        ub = u * G
        vb = v * G
        for x in range(G):
            a = ub + x
            b = vb + T[x][s]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _lift_cost(N0, base_edges, G, T, volt, D):
    return _bad_pairs_bits(N0 * G, _lift_adj(N0, base_edges, G, T, volt), D)


def _lift_edges(N0, base_edges, G, T, volt):
    E = []
    for idx, (u, v) in enumerate(base_edges):
        s = volt[idx]
        for x in range(G):
            E.append((u * G + x, v * G + T[x][s]))
    return N0 * G, E


def _anneal_lift(N0, base_edges, free, G, T, D, rng, deadline):
    """Simulated annealing over the free voltages. Returns (success, voltages)."""
    volt = [0] * len(base_edges)
    for idx in free:
        volt[idx] = rng.randrange(G)
    cost = _lift_cost(N0, base_edges, G, T, volt, D)
    temp = max(2.0, 0.01 * cost)
    while cost > 0 and free and time.monotonic() < deadline:
        temp = max(0.5, temp * 0.999)
        idx = free[rng.randrange(len(free))]
        old = volt[idx]
        new = rng.randrange(G)
        if new == old:
            continue
        volt[idx] = new
        c2 = _lift_cost(N0, base_edges, G, T, volt, D)
        limit = cost - temp * math.log(1.0 - rng.random())
        if c2 <= limit:
            cost = c2
        else:
            volt[idx] = old
    return cost == 0, volt


def _group_tables(G, rng, limit):
    """Multiplication tables of up to `limit` semidirect products Z_m x| Z_k of order G."""
    options = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        if m == 1:
            options.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                options.append((m, k, r))
    rng.shuffle(options)
    tables = []
    for m, k, r in options[:limit]:
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if order != G:
            continue
        tables.append([[mul(x, g) for g in range(G)] for x in range(G)])
    return tables


def _lift_search(N0, base_edges, D, rng, deadline, start_G, consider):
    """Try lifts of increasing order G, keeping each success. Stop at the first G that fails."""
    tree = _tree_edges(N0, base_edges)
    free = [i for i in range(len(base_edges)) if i not in tree]
    G = start_G
    while True:
        if deadline - time.monotonic() < 1.0:
            break
        tables = _group_tables(G, rng, 4)
        found = False
        for T in tables:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            budget = max(1.5, remaining * 0.3)
            stop = min(deadline, time.monotonic() + budget)
            ok, volt = _anneal_lift(N0, base_edges, free, G, T, D, rng, stop)
            if ok:
                n, e = _lift_edges(N0, base_edges, G, T, volt)
                consider(n, e)
                found = True
                break
        if not found:
            break
        G += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    q = d - 1
    prime_power_q = q >= 2 and lib.is_prime_power(q)

    if D >= 3:
        # Projective plane incidence graph: degree d, diameter 3.
        if prime_power_q and 2 * (q * q + q + 1) <= 3000:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
        # Araujo-Pardo-Lopez record graph when d - 2 is a prime power.
        q2 = d - 2
        if 3 <= q2 <= 16 and lib.is_prime_power(q2):
            try:
                ar = lib.araujo_lopez_graph(q2)
                consider(ar[0], ar[1])
            except Exception:
                pass

    # Main family for D >= 5: lifts of PG(2, q) over groups of growing order.
    if D >= 5 and prime_power_q and 2 * (q * q + q + 1) <= 400:
        N0, base_edges = lib.projective_plane_incidence(q)
        start_G = max(2, best_n // N0 + 1)
        _lift_search(N0, base_edges, D, rng, deadline, start_G, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
