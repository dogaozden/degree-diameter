import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Plain algebraic bases: projective plane (D=3) and generalized quadrangle (D=4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
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
            for attempt in range(60):
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
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
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
# NEW family: free bipartite base multigraph lifted by a cyclic group Z_m.
#
# Base: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. A dart (i, j, a)
# joins A_i,g to B_j,(g+a) mod m for every g. The base is d-regular: d layers,
# each layer a permutation p_L of range(b), giving darts (i, p_L[i], a).
# The lift has 2*b*m vertices, degree d, and is bipartite by construction.
#
# Z_m acts by translation and transitively on each fibre, so the diameter
# check only needs BFS from A_i,0 and B_j,0: 2b sources instead of 2bm.
# The base multigraph and voltages are annealed jointly.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _lift_cost(b, m, D, darts):
    """Unreached (source, vertex) pairs from the 2b fibre representatives. Zero means valid."""
    if len({(i, j, a) for i, j, a in darts}) < len(darts):
        return _BIG
    N = 2 * b * m
    adj = [[] for _ in range(N)]
    for i, j, a in darts:
        base_a = i * m
        base_b = (b + j) * m
        for g in range(m):
            x = base_a + g
            y = base_b + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    reps = [i * m for i in range(b)] + [(b + j) * m for j in range(b)]
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


def _lift_edges(b, m, darts):
    E = []
    for i, j, a in darts:
        for g in range(m):
            E.append((i * m + g, (b + j) * m + (g + a) % m))
    return 2 * b * m, E


def _anneal_lift(d, D, b, m, rng, deadline, iters):
    """Anneal base multigraph (layer permutations) and Z_m voltages jointly."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(b), b)
        for i in range(b):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _lift_cost(b, m, D, [tuple(x) for x in darts])

    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * ((T1 / T0) ** (it / iters))

        if rng.random() < 0.6 or b == 1:
            # Voltage move.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _lift_cost(b, m, D, [tuple(x) for x in darts])
            delta = c2 - cost
            if delta <= 0 or (delta / T < 50 and rng.random() < math.exp(-delta / T)):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            # Base move: swap two B-targets within one layer (keeps the layer a permutation).
            L = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            x, y = L * b + i1, L * b + i2
            darts[x][1], darts[y][1] = darts[y][1], darts[x][1]
            c2 = _lift_cost(b, m, D, [tuple(t) for t in darts])
            delta = c2 - cost
            if delta <= 0 or (delta / T < 50 and rng.random() < math.exp(-delta / T)):
                cost = c2
            else:
                darts[x][1], darts[y][1] = darts[y][1], darts[x][1]

    if cost == 0:
        return [tuple(t) for t in darts]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # Algebraic bases and their grown versions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)

    # Main bold search: annealed base-multigraph lifts over Z_m, aiming just above best_n.
    bound = lib._moore_bound(d, D)
    attempt_len = max(2.0, 0.08 * time_limit)
    if d >= 2 and D >= 3:
        while time.monotonic() < deadline:
            b_choices = [b for b in range(2, 13) if 2 * b * (best_n // (2 * b) + 1) <= bound]
            if not b_choices:
                break
            b = rng.choice(b_choices)
            m = best_n // (2 * b) + 1 + rng.randrange(0, 2)
            if 2 * b * m > bound or m < 2:
                continue
            att_deadline = min(deadline, time.monotonic() + attempt_len)
            darts = _anneal_lift(d, D, b, m, rng, att_deadline, iters=6000)
            if darts is not None:
                n, e = _lift_edges(b, m, darts)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
