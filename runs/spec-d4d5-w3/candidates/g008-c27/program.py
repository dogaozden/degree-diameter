import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions of time_limit. Group-lift search ends at FRAC_GROUP; the
# insert-and-repair stage runs until FRAC_REPAIR.
# ----------------------------------------------------------------------------
FRAC_GROUP = 0.55
FRAC_REPAIR = 0.88
REPAIR_FAILS = 6
REPAIR_ITERS = 1500
EXC_WEIGHT = 5
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic base: projective plane incidence (D = 3 record family).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _adj_from_edges(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable counts)."""
    reach = _balls_radius(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    adj = _adj_from_edges(n, edges)
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
    adj = _adj_from_edges(n, edges)
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
# NEW: penalised insert-and-repair annealing.
#
# Idea: a valid D-diameter graph is grown by one vertex at a time. The new
# vertex v is given d edges to the opposite side even though this may push
# some neighbours above degree d. The state is then annealed with three moves:
#   * rewire one endpoint of an edge to another vertex of the same side
#     (this moves degree slack and removes overflow),
#   * add an edge between two spare opposite-side vertices (never hurts),
#   * delete an edge (frees slack at a distance cost).
# Cost = (#pairs farther than D) + EXC_WEIGHT * (total degree overflow).
# Cost 0 means a valid graph with one more vertex. The state is kept in place
# and the previous valid state is restored when the annealing fails.
# ----------------------------------------------------------------------------

def _pen_cost(n, nbr, d, D):
    exc = 0
    for s in nbr:
        if len(s) > d:
            exc += len(s) - d
    adj = [list(s) for s in nbr]
    return _bad_count(n, adj, D) + EXC_WEIGHT * exc


def _repair_anneal(n, color, nbr, E, d, D, deadline, rng, iters):
    """Anneal (nbr, E) in place. Returns True if cost reaches 0."""
    side = [[v for v in range(n) if color[v] == 0],
            [v for v in range(n) if color[v] == 1]]
    cost = _pen_cost(n, nbr, d, D)
    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if cost == 0:
            return True
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        r = rng.random()

        if r < 0.10:  # add an edge between two spare opposite vertices
            x = rng.choice(side[0])
            y = rng.choice(side[1])
            if len(nbr[x]) >= d or len(nbr[y]) >= d or y in nbr[x]:
                continue
            nbr[x].add(y)
            nbr[y].add(x)
            E.append((x, y))
            cost = _pen_cost(n, nbr, d, D)
            continue

        if r < 0.15 and E:  # delete an edge
            i = rng.randrange(len(E))
            a, b = E[i]
            nbr[a].discard(b)
            nbr[b].discard(a)
            c2 = _pen_cost(n, nbr, d, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                E[i] = E[-1]
                E.pop()
                cost = c2
            else:
                nbr[a].add(b)
                nbr[b].add(a)
            continue

        if not E:
            continue
        # rewire one endpoint of a random edge (E keeps its size)
        i = rng.randrange(len(E))
        a, b = E[i]
        if rng.random() < 0.5:
            x, fixed = b, a            # move the side-1 endpoint
            y = rng.choice(side[1])
        else:
            x, fixed = a, b            # move the side-0 endpoint
            y = rng.choice(side[0])
        if y == x or y in nbr[fixed]:
            continue
        nbr[x].discard(fixed)
        nbr[fixed].discard(x)
        nbr[y].add(fixed)
        nbr[fixed].add(y)
        c2 = _pen_cost(n, nbr, d, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = (fixed, y) if x == b else (y, fixed)
        else:
            nbr[y].discard(fixed)
            nbr[fixed].discard(y)
            nbr[x].add(fixed)
            nbr[fixed].add(x)
    return cost == 0


def _insert_repair(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex and repair with _repair_anneal; returns the largest valid graph."""
    adj = _adj_from_edges(n, edges)
    color = _bipartition(n, adj)
    cur_n = n
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    best = (n, [tuple(e) for e in edges])
    fails = 0
    while time.monotonic() < deadline and fails < REPAIR_FAILS:
        snap_E = list(E)
        snap_color = list(color)
        c = rng.randrange(2)
        v = cur_n
        color2 = color + [c]
        nbr = [set() for _ in range(cur_n + 1)]
        for a, b in E:
            nbr[a].add(b)
            nbr[b].add(a)
        others = [u for u in range(cur_n) if color[u] != c]
        rng.shuffle(others)
        others.sort(key=lambda u: len(nbr[u]))
        for u in others[:d]:
            nbr[u].add(v)
            nbr[v].add(u)
            E.append((u, v) if c == 1 else (v, u))
        ok = _repair_anneal(cur_n + 1, color2, nbr, E, d, D, deadline, rng, REPAIR_ITERS)
        if ok:
            cur_n += 1
            color = color2
            best = (cur_n, [tuple(e) for e in E])
            fails = 0
        else:
            E = snap_E
            color = snap_color
            fails += 1
    return best


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed.
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


def _edges_lift(k, G, darts, perms):
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    group_deadline = start + FRAC_GROUP * time_limit
    repair_deadline = start + FRAC_REPAIR * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, [tuple(x) for x in e])

    # Algebraic base for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if pg[0] >= moore:
                return best
            consider(_grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng))

    # Group voltage-lift search.
    try:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500 if D >= 5 else 400
        while time.monotonic() < group_deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, group_deadline, anneal_iters)
            if res is not None:
                consider(res)
                grow_end = min(group_deadline, time.monotonic() + 0.05 * time_limit)
                consider(_grow(res[0], res[1], d, D, grow_end, rng))
    except Exception:
        pass

    # Insert-and-repair on the best graph found so far.
    try:
        if best[0] < moore and time.monotonic() < repair_deadline:
            grow_end = min(repair_deadline, time.monotonic() + 0.03 * time_limit)
            consider(_grow(best[0], best[1], d, D, grow_end, rng))
            consider(_insert_repair(best[0], best[1], d, D, repair_deadline, rng))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
