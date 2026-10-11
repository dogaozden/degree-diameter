import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
            for attempt in range(100):
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
# NEW: insertion of a vertex pair into a d-regular bipartite graph, followed by
# degree-preserving edge-swap annealing on the number of bad pairs.
#
# Insertion: pick an edge (a, b) with a on side 0 and b on side 1. Replace it by
# (a, y) and (x, b), where x is a new side-0 vertex and y a new side-1 vertex.
# Each move gives one edge to x and one to y, and leaves every old degree
# unchanged. After d moves, x and y both have degree d, so the graph stays
# d-regular and bipartite. The graph is then repaired by edge-swaps, which
# also keep all degrees fixed, until every pair is within distance D.
# ----------------------------------------------------------------------------

def _bad_count(n, E, D):
    """Number of unordered vertex pairs at distance more than D (edges E as [side0, side1] pairs)."""
    nbr = [[] for _ in range(n)]
    for a, b in E:
        nbr[a].append(b)
        nbr[b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in nbr[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _try_insert(n, E, d, D, rng, iters, deadline):
    """Insert one vertex pair into the regular graph E, then anneal by edge swaps.

    Returns (n + 2, edges) with zero bad pairs, or None on failure.
    """
    x, y = n, n + 1
    E2 = [[a, b] for a, b in E]
    S2 = {(a, b) for a, b in E2}
    xn, yn = set(), set()
    tries = 0
    while len(xn) < d:
        tries += 1
        if tries > 20000:
            return None
        i = rng.randrange(len(E2))
        a, b = E2[i]
        if b in xn or a in yn:
            continue
        S2.discard((a, b))
        S2.add((a, y))
        E2[i] = [a, y]
        E2.append([x, b])
        S2.add((x, b))
        xn.add(b)
        yn.add(a)

    N = n + 2
    m = len(E2)
    cost = _bad_count(N, E2, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = 0.6 * (1.0 - it / iters) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E2[i]
        a2, b2 = E2[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S2 or (a2, b1) in S2:
            continue
        S2.discard((a1, b1))
        S2.discard((a2, b2))
        S2.add((a1, b2))
        S2.add((a2, b1))
        E2[i] = [a1, b2]
        E2[j] = [a2, b1]
        c2 = _bad_count(N, E2, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            S2.discard((a1, b2))
            S2.discard((a2, b1))
            S2.add((a1, b1))
            S2.add((a2, b2))
            E2[i] = [a1, b1]
            E2[j] = [a2, b2]
    if cost != 0:
        return None
    return N, E2


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _grow_regular(n, edges, d, D, deadline, rng, consider):
    """Repeatedly insert vertex pairs into a regular bipartite graph while it stays valid."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    cur_n = n
    cur_E = [[u, v] if color[u] == 0 else [v, u] for u, v in edges]
    while time.monotonic() < deadline:
        res = _try_insert(cur_n, cur_E, d, D, rng, 3000, deadline)
        if res is None:
            continue
        cur_n, cur_E = res
        consider(cur_n, [(a, b) for a, b in cur_E])


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
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
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    pool = []  # all valid graphs found, for choosing a regular base later

    def consider(n, e):
        nonlocal best, best_n
        if not lib.is_valid(n, e, d, D):
            return
        pool.append((n, e))
        if n > best_n:
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)

    # Phase 1: annealed group voltage lifts, targeted just above the current best order.
    phase1_end = start + (0.4 if D >= 5 else 0.6) * time_limit
    ks = [1, 1, 2, 2, 3, 4]
    anneal_iters = 1500
    while time.monotonic() < phase1_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, phase1_end, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: NEW insertion-and-swap growth from the largest regular valid graph.
    regs = [g for g in pool if _is_regular(g[0], g[1], d)]
    if regs:
        n0, e0 = max(regs, key=lambda g: g[0])
    else:
        n0, e0 = lib.haar_graph(d, range(d))
    _grow_regular(n0, e0, d, D, total_deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
