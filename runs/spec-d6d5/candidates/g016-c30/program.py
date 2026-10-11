import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane incidence, Araujo-Pardo-Lopez (D = 3),
# arc extensions of PG(2, q), and greedy cover growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
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
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(4):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
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
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
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
# Group choice.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices=None):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


# ----------------------------------------------------------------------------
# NEW: layered bi-Cayley lifts with base-layer splicing.
#
# A lift over a group of order G with k base vertices per side is described by
# d "layers". Each layer is a perfect matching between A_0..A_{k-1} and
# B_0..B_{k-1}, stored as darts [a, b, s]: the dart joins A_{a,x} to
# B_{b, x*s} for every group element x. Each vertex then has degree d (one
# dart per layer), and the group acts by left translation, so one
# representative per base block suffices for the diameter test.
#
# Splicing (new construction): from a valid lift on k base vertices, add one
# new A block and one new B block. In every layer, pick a dart (a, x, s),
# delete it and add (a, new_B, s1) and (new_A, x, s2). The result is a valid
# bi-Cayley structure on k+1 base vertices with the same group, degree d and
# order 2(k+1)G. We then anneal the new voltages. A chain of successful
# splices grows the graph by whole group blocks.
# ----------------------------------------------------------------------------

_INF = float("inf")
_REPAIR_MAX = 60


def _lrandom(d, k, G, rng):
    """Random layers: d perfect matchings between k A-blocks and k B-blocks, random voltages."""
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        layers.append([[a, p[a], rng.randrange(G)] for a in range(k)])
    return layers


def _splice(k, G, layers, rng):
    """Add one A-block and one B-block (index k) to a k-block lift; returns layers for k+1 blocks."""
    out = [[list(x) for x in L] for L in layers]
    for L in out:
        idx = rng.randrange(len(L))
        a, x, _ = L.pop(idx)
        L.append([a, k, rng.randrange(G)])
        L.append([k, x, rng.randrange(G)])
    return out


def _layers_adj(k, G, layers, rt):
    """Adjacency lists of the lift. rt[s][x] = x * s in the group."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for L in layers:
        for a, b, s in L:
            pm = rt[s]
            ba = a * G
            bb = (k + b) * G
            for g in range(G):
                x = ba + g
                y = bb + pm[g]
                adj[x].append(y)
                adj[y].append(x)
    return adj


def _lcost(k, G, D, adj, limit=_INF):
    """Unreached (representative, vertex) pairs within distance D; stops early above limit."""
    N = len(adj)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _lanneal(D, k, G, rt, layers, rng, deadline, iters, T0):
    """Annealing over voltages and per-layer B-assignments. Mutates layers; returns final cost."""
    cost = _lcost(k, G, D, _layers_adj(k, G, layers, rt))
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        L = layers[rng.randrange(len(layers))]
        if rng.random() < 0.6:
            idx = rng.randrange(len(L))
            old = L[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            L[idx][2] = new
            c2 = _lcost(k, G, D, _layers_adj(k, G, layers, rt), limit)
            if c2 <= limit:
                cost = c2
            else:
                L[idx][2] = old
        else:
            if len(L) < 2:
                continue
            i1, i2 = rng.sample(range(len(L)), 2)
            L[i1][1], L[i2][1] = L[i2][1], L[i1][1]
            c2 = _lcost(k, G, D, _layers_adj(k, G, layers, rt), limit)
            if c2 <= limit:
                cost = c2
            else:
                L[i1][1], L[i2][1] = L[i2][1], L[i1][1]
    return cost


def _layers_to_edges(k, G, layers, rt):
    """Explicit (n, edges) of the lift. A-vertices come first, so every edge is (small, large)."""
    E = set()
    for L in layers:
        for a, b, s in L:
            pm = rt[s]
            for g in range(G):
                E.add((a * G + g, (k + b) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.05 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        for n_c, e_c in _arc_extensions(d, start + 0.1 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        pool = []  # successful layered states: (k, G, rt, layers), sorted by k*G descending
        ks = [1, 1, 2, 2, 3]
        k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

        def record(k, G, rt, layers):
            """Store a valid lift (after saturation) and keep it as a splice seed."""
            N, E = _layers_to_edges(k, G, layers, rt)
            e2 = _saturate_edges(N, E, d, rng)
            if lib.is_valid(N, e2, d, D):
                consider(N, e2)
                pool.append((k, G, rt, [[list(x) for x in L] for L in layers]))
                pool.sort(key=lambda t: -(t[0] * t[1]))
                del pool[24:]

        def try_repair(k, G, rt, layers):
            """Near miss: delete far-off vertices, then saturate and consider."""
            N, E = _layers_to_edges(k, G, layers, rt)
            rep = _repair(N, E, D, min(deadline, time.monotonic() + 4.0), rng)
            if rep is not None:
                n3, e3 = rep
                consider(n3, _saturate_edges(n3, e3, d, rng))

        while time.monotonic() < deadline:
            if pool and rng.random() < 0.6:
                # Grow: splice a successful lift by one base block, keep G fixed.
                k0, G0, rt0, lay0 = rng.choice(pool[:4])
                k1 = k0 + 1
                lay1 = _splice(k0, G0, lay0, rng)
                cost = _lanneal(D, k1, G0, rt0, lay1, rng, deadline, 600, 0.5)
                if cost == 0:
                    record(k1, G0, rt0, lay1)
                elif cost <= _REPAIR_MAX and rng.random() < 0.3:
                    try_repair(k1, G0, rt0, lay1)
                continue

            # Fresh search: random layered lift over a random group of order near record/k.
            k = rng.choice(ks)
            base = best_n // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 6)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng, k2_pool if rng.random() < 0.8 else None)
            if g is None:
                continue
            order, mul = g
            rt = [[mul(x, s) for x in range(order)] for s in range(order)]
            layers = _lrandom(d, k, order, rng)
            iters = 1200 if k == 1 else 400
            cost = _lanneal(D, k, order, rt, layers, rng, deadline, iters, 1.0)
            if cost == 0:
                record(k, order, rt, layers)
            elif cost <= _REPAIR_MAX and rng.random() < 0.3:
                try_repair(k, order, rt, layers)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
