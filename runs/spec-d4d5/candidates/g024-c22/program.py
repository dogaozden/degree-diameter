import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Common helpers.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a graph given by adjacency lists (-1 only for isolated unseen vertices)."""
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


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2 (annealed), used to seed the search.
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
# NEW: degree-preserving switch annealing on bipartite graphs.
#
# State: a bipartite graph with max degree d. Cost = number of unordered vertex
# pairs at distance > D (computed with bitmask balls). Moves:
#   * switch: edges (a,b),(c,e) with a,c on the left become (a,e),(c,b);
#     this keeps every degree and bipartiteness, and is undone exactly on reject;
#   * add: join a random deficient left/right pair (used after growing).
# Growth: append one left and one right vertex, fill spare degree greedily,
# then anneal until the cost is zero. Each success is a larger valid graph.
# ----------------------------------------------------------------------------

def _bad_count(n, nb, D):
    """Number of unordered pairs at distance > D, from neighbour sets nb."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in nb[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(n, edges, col, d, rng):
    """Greedily join deficient opposite-colour vertices in random order."""
    E = [tuple(e) for e in edges]
    deg = [0] * n
    existing = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def _switch_anneal(n, edges, col, d, D, deadline, rng):
    """Anneal a bipartite graph with switches/adds until its cost is 0 or time runs out.

    Returns (cost, edges). The edge list is always a valid-degree bipartite graph.
    """
    nb = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        if col[u] == 1:
            u, v = v, u
        E.append([u, v])
        nb[u].add(v)
        nb[v].add(u)
    deg = [len(s) for s in nb]
    left = [v for v in range(n) if col[v] == 0]
    right = [v for v in range(n) if col[v] == 1]
    cost = _bad_count(n, nb, D)
    if cost == 0 or len(E) < 2:
        return cost, [(u, v) for u, v in E]

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T0, T1 = 2.0, 0.05
    T = T0
    it = 0
    while cost > 0:
        if it & 15 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        it += 1

        if rng.random() < 0.05:
            # Add move between deficient vertices of opposite colour.
            dl = [a for a in left if deg[a] < d]
            dr = [b for b in right if deg[b] < d]
            if not dl or not dr:
                continue
            a = rng.choice(dl)
            b = rng.choice(dr)
            if b in nb[a]:
                continue
            nb[a].add(b)
            nb[b].add(a)
            deg[a] += 1
            deg[b] += 1
            E.append([a, b])
            c2 = _bad_count(n, nb, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                E.pop()
                nb[a].discard(b)
                nb[b].discard(a)
                deg[a] -= 1
                deg[b] -= 1
        else:
            # Degree-preserving switch.
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in nb[a] or b in nb[c]:
                continue
            nb[a].discard(b)
            nb[b].discard(a)
            nb[c].discard(e)
            nb[e].discard(c)
            nb[a].add(e)
            nb[e].add(a)
            nb[c].add(b)
            nb[b].add(c)
            E[i] = [a, e]
            E[j] = [c, b]
            c2 = _bad_count(n, nb, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                nb[a].discard(e)
                nb[e].discard(a)
                nb[c].discard(b)
                nb[b].discard(c)
                nb[a].add(b)
                nb[b].add(a)
                nb[c].add(e)
                nb[e].add(c)
                E[i] = [a, b]
                E[j] = [c, e]

    return cost, [(u, v) for u, v in E]


def _grow_switch(n, edges, d, D, deadline, rng, consider):
    """Repeatedly add two vertices (one per side) and anneal them into a valid graph."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline - 0.5:
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        col = _bipartition(cur_n, adj)
        col = [c if c >= 0 else 0 for c in col]
        n2 = cur_n + 2
        col2 = col + [0, 1]
        e2 = _fill(n2, cur_e, col2, d, rng)
        now = time.monotonic()
        stage_end = min(deadline, now + max(3.0, 0.5 * (deadline - now)))
        cost, E = _switch_anneal(n2, e2, col2, d, D, stage_end, rng)
        if cost == 0:
            cur_n, cur_e = n2, E
            consider(n2, E)


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib._moore_bound(d, D):
        return best

    if D >= 3:
        # Phase 1: annealed group voltage lifts seed the search.
        p1 = start + 0.3 * time_limit
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            iters = 1500
        else:
            ks = [1, 1, 2, 3]
            iters = 400
        while time.monotonic() < p1:
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
            res = _anneal(d, D, k, order, mul, rng, p1, iters)
            if res is not None:
                consider(res[0], res[1])
            if best_n >= lib._moore_bound(d, D):
                return best

        # Phase 2: NEW switch-annealing growth from the best valid graph found so far.
        _grow_switch(best_n, best[1], d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
