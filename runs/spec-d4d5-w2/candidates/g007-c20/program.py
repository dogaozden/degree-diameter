import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic helpers.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _graph_adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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


def _balls_radius(n, adj, r):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all old vertices within distance D-1.

    Every added vertex reaches every old vertex within D, and no existing
    distance shrinks or breaks, so validity is preserved.
    """
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _graph_adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(30):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices. Adding edges never breaks diameter or bipartiteness."""
    edges = list(edges)
    adj = _graph_adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g   and   B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,(g*s) for every g.
# Left multiplication is an automorphism that is transitive on each layer,
# so distances need only be checked from one representative per layer.
# Each layer of d darts is a permutation i -> j, so the lift is d-regular.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, table) with table[s][g] = g*s for a random Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12])
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
        table = [[mul(g, s) for g in range(order)] for s in range(order)]
        return order, table
    return None


def _cost(k, G, D, darts, table):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        row = table[s]
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + row[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, table):
    E = set()
    for i, j, s in darts:
        row = table[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + row[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, table, rng, deadline, iters):
    """Simulated annealing over dart voltages and per-layer target assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, table)
    if cost == 0:
        return _edges(k, G, darts, table)

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
            darts[idx][2] = new_s
            c2 = _cost(k, G, D, darts, table)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, table)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, table)
    return None


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def _build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane base (diameter 3), grown by cover extension.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                n2, e2 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
                consider(n2, e2)
                break

    if D <= 3:
        return best

    # Bold change: bi-Cayley voltage lifts over semidirect products, targeted
    # just above the current best order. Each success is grown by cover extension.
    main_deadline = start + 0.85 * time_limit
    ks = [1, 1, 2, 2, 3, 4]
    iters = 2000 if D >= 5 else 800
    while time.monotonic() < main_deadline:
        k = rng.choice(ks)
        G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, table = g
        res = _anneal(d, D, k, order, table, rng, main_deadline, iters)
        if res is not None:
            consider(res[0], res[1])
            gn, ge = _grow(res[0], res[1], d, D, start + 0.93 * time_limit, rng)
            consider(gn, ge)

    gn, ge = _grow(best[0], best[1], d, D, start + 0.93 * time_limit, rng)
    consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    fallback = lib.haar_graph(d, range(d))
    try:
        n, edges = _build(d, D, seed, time_limit)
    except Exception:
        return fallback
    if not lib.is_valid(n, edges, d, D):
        return fallback
    return n, edges
