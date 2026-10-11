import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and cover-based vertex extension.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(200):
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: degree-respecting annealed edge repair for diameter.
#
# Given a bipartite graph whose vertices have degree <= d, we add a pair of new
# vertices (one per side) and anneal the edge set so that the number of vertex
# pairs at distance > D drops to zero. Moves are:
#   - add:      join a spare A vertex to a spare B vertex;
#   - subdivide: take an edge (a, b), move its B end to a spare A vertex x,
#                and join a to a spare B vertex y (net +1 edge, degrees of
#                old vertices unchanged);
#   - swap:     2-switch of two edges (degree preserving).
# Cost = number of unordered pairs at distance > D (lib-style bitmask BFS).
# ----------------------------------------------------------------------------

def _bad_pairs_adj(n, adj, D):
    """Number of unordered vertex pairs at distance > D, from adjacency sets."""
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


def _apply(adj, op):
    kind, x, y = op
    if kind == "add":
        adj[x].add(y)
        adj[y].add(x)
    else:
        adj[x].discard(y)
        adj[y].discard(x)


def _inverse(op):
    kind, x, y = op
    return ("rem" if kind == "add" else "add", x, y)


def _repair_run(n, color, adj, d, D, deadline, rng):
    """Anneal `adj` in place until all pairs are within D. Returns True on success."""
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    cost = _bad_pairs_adj(n, adj, D)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 7) == 0 and time.monotonic() > deadline:
            return False
        T = max(0.2, T * 0.9995)
        spA = [v for v in A if len(adj[v]) < d]
        spB = [v for v in B if len(adj[v]) < d]
        mv = rng.random()
        ops = None
        if mv < 0.3:
            if not spA or not spB:
                continue
            x = rng.choice(spA)
            y = rng.choice(spB)
            if y in adj[x]:
                continue
            ops = [("add", x, y)]
        elif mv < 0.7:
            if not spA:
                continue
            a = rng.choice(A)
            if not adj[a]:
                continue
            b = rng.choice(list(adj[a]))
            x = rng.choice(spA)
            if x == a or b in adj[x]:
                continue
            cand = [y for y in spB if y != b and y not in adj[a]]
            if not cand:
                continue
            y = rng.choice(cand)
            ops = [("rem", a, b), ("add", x, b), ("add", a, y)]
        else:
            a1 = rng.choice(A)
            a2 = rng.choice(A)
            if not adj[a1] or not adj[a2]:
                continue
            b1 = rng.choice(list(adj[a1]))
            b2 = rng.choice(list(adj[a2]))
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            ops = [("rem", a1, b1), ("rem", a2, b2),
                   ("add", a1, b2), ("add", a2, b1)]
        for op in ops:
            _apply(adj, op)
        new = _bad_pairs_adj(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            for op in reversed(ops):
                _apply(adj, _inverse(op))
    return True


def _grow_repair(n, edges, d, D, deadline, rng):
    """Repeatedly add one A and one B vertex and repair by annealing; keep the last valid graph."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    best = (n, list(edges))
    while time.monotonic() < deadline:
        n2 = n + 2
        adj2 = [set(s) for s in adj] + [set(), set()]
        color2 = color + [0, 1]
        remaining = deadline - time.monotonic()
        sub = min(deadline, time.monotonic() + max(3.0, 0.6 * remaining))
        if not _repair_run(n2, color2, adj2, d, D, sub, rng):
            break
        E = [(a, b) for a in range(n2) for b in adj2[a] if a < b]
        if not lib.is_valid(n2, E, d, D):
            break
        best = (n2, E)
        n, adj, color = n2, adj2, color2
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph is d-regular, diameter 3.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            consider(*_grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng))
        # NEW: grow the best base by pairs of vertices, repairing diameter by annealing.
        consider(*_grow_repair(best[0], best[1], d, D, deadline, rng))
        return best

    # D >= 4 (and other cases): cover growth from projective plane, then voltage lifts.
    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)
        consider(*_grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng))

    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
