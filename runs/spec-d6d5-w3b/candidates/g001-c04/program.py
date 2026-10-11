import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane incidence graph and Araujo-Pardo-Lopez for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Shared graph utilities (bitset balls, bipartition, adjacency sets).
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _colour(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _adj_of(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _compact(n, edges, keep):
    """Relabel kept vertices to 0..m-1 and keep only edges between them."""
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = _adj_of(cur_n, cur_e)
        ball = _balls(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


# ----------------------------------------------------------------------------
# NEW: swap-annealed growth.
#
# Append `add_pairs` new A-vertices and B-vertices, seed them with whatever
# spare degree exists, then anneal over two kinds of moves that keep the
# graph bipartite and within max degree d:
#   * degree-preserving bipartite 2-switches,
#   * endpoint reattachment (move one end of an edge to another vertex of the
#     same side that has spare degree), which lets new vertices gain edges.
# The cost is the number of unordered pairs at distance > D. Cost 0 means the
# grown graph is valid. This replaces greedy covering: it can trade existing
# edges for new ones instead of only using leftover degree.
# ----------------------------------------------------------------------------

def _apply(adj, rem, add):
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


def _move_switch(adj, As, rng):
    a1 = rng.choice(As)
    a2 = rng.choice(As)
    if a1 == a2 or not adj[a1] or not adj[a2]:
        return None
    b1 = rng.choice(list(adj[a1]))
    b2 = rng.choice(list(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    rem = [(a1, b1), (a2, b2)]
    add = [(a1, b2), (a2, b1)]
    _apply(adj, rem, add)
    return rem, add


def _move_reattach(adj, sides, d, rng):
    pool = sides[rng.randrange(2)]
    u = rng.choice(pool)
    if not adj[u]:
        return None
    v = rng.choice(list(adj[u]))
    cands = [w for w in pool if w != u and len(adj[w]) < d and w not in adj[v]]
    if not cands:
        return None
    w = rng.choice(cands)
    rem = [(u, v)]
    add = [(w, v)]
    _apply(adj, rem, add)
    return rem, add


def _grow_swap(n, edges, d, D, add_pairs, deadline, rng):
    """Grow a bipartite graph by add_pairs A/B vertex pairs and anneal to diameter <= D.

    Returns (n, edges) with zero unreachable pairs, or None if the deadline passes first.
    """
    if add_pairs < 1:
        return None
    adj = _adj_of(n, edges)
    col = _colour(n, adj)
    N = n + 2 * add_pairs
    adj += [set() for _ in range(2 * add_pairs)]
    side = col + [k % 2 for k in range(2 * add_pairs)]  # new even index -> A, odd -> B
    sides = [[v for v in range(N) if side[v] == 0],
             [v for v in range(N) if side[v] == 1]]
    As = sides[0]

    # Seed new vertices with available spare degree.
    for x in range(n, N):
        cands = [v for v in sides[1 - side[x]] if len(adj[v]) < d and v not in adj[x]]
        rng.shuffle(cands)
        for v in cands:
            if len(adj[x]) >= d:
                break
            if len(adj[v]) < d:
                adj[x].add(v)
                adj[v].add(x)

    def cost():
        balls = _balls(N, adj, D)
        return sum(N - b.bit_count() for b in balls) // 2

    cur = cost()
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        T = max(0.1, T * 0.999)
        if rng.random() < 0.5:
            mv = _move_switch(adj, As, rng)
        else:
            mv = _move_reattach(adj, sides, d, rng)
        if mv is None:
            continue
        rem, add = mv
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _apply(adj, add, rem)
    if cur != 0:
        return None
    E = [(a, b) for a in sides[0] for b in adj[a]]
    return N, E


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Left multiplication is an automorphism, so one representative per side and
# layer suffices for the cost.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng, k2_choices):
    """(order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, start=None, T0=1.0):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (edges_or_None, darts, cost).
    """
    if start is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
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
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D < 5 or d < 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # ---- Target path (D >= 5): voltage-lift search, then swap-annealed growth.
    lift_deadline = start + 0.55 * time_limit
    grow_deadline = start + 0.85 * time_limit

    ks = [1, 1, 1, 2, 2, 3, 4]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    k2_any = [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    elite = {}      # (k, order) -> (cost, darts, mul)
    cands = []      # valid repaired graphs, grown later

    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + (max(3, lo // 4) if k == 1 else max(3, lo // 8))
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool) if rng.random() < 0.8 else None
        if g is None:
            g = _sample_group(G, rng, k2_any)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_darts, T0, mul_use = None, 1.0, mul
        if key in elite and rng.random() < 0.5:
            _, st, mul_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1500 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, lift_deadline,
                                    iters, start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.5 and time.monotonic() < lift_deadline:
            perms = [_right_perm(mul_use, order, s) for _, _, s in darts_out]
            N, E = _edges(k, order, darts_out, perms)
            rep = _repair(N, E, D, min(lift_deadline, time.monotonic() + 3.0), rng)
            if rep is not None and lib.is_valid(rep[0], rep[1], d, D):
                consider(rep[0], rep[1])
                cands.append(rep)

    # Growth stage: grow the largest valid graphs by swap-annealed pair additions.
    pool = [best] + cands
    while time.monotonic() < grow_deadline:
        pool.sort(key=lambda g: -g[0])
        pool = pool[:8]
        idx = min(len(pool) - 1, int(rng.random() ** 2 * len(pool)))
        src = pool[idx]
        add = rng.choice([1, 2, 3, 4, 6])
        dl = min(grow_deadline, time.monotonic() + 5.0)
        out = _grow_swap(src[0], src[1], d, D, add, dl, rng)
        if out is not None and lib.is_valid(out[0], out[1], d, D):
            pool.append(out)
            consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
