import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Phase 1: known constructions (projective plane, generalized quadrangle),
# cover-based growth, and non-cyclic group lifts.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
    """Extend by cover vertices first, then saturate edges with spare degree."""
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


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Phase 2 (new): edge-switch annealing that grows the vertex count.
#
# State: a bipartite graph stored as E = list of (side0, side1) edges, with
# degrees <= d. Moves:
#   - saturate: join spare-degree opposite vertices (never raises cost);
#   - degree-preserving double edge switch, accepted by Metropolis on the
#     number of vertex pairs at distance > D.
# Once cost reaches 0 the graph is valid; a new point/line pair is then
# attached by stealing edges, and the search continues at the larger order.
# ----------------------------------------------------------------------------

def _key(x, y, color):
    """Edge key oriented as (side0, side1)."""
    return (x, y) if color[x] == 0 else (y, x)


def _count_bad(n, E, D):
    """Number of unordered vertex pairs at distance > D (unreachable counted)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _attach(v, E, ES, deg, color, d, rng):
    """Give new vertex v (no edges yet) up to d neighbours on the opposite side.

    Uses free partners when available; otherwise steals an edge (p, q), keeping
    the partner-side endpoint w and giving the other endpoint one less degree.
    """
    N = len(color)
    partner = 1 - color[v]
    for _ in range(d):
        if deg[v] >= d:
            break
        free = [u for u in range(N)
                if color[u] == partner and deg[u] < d and _key(v, u, color) not in ES]
        if free:
            u = rng.choice(free)
            k = _key(v, u, color)
            E.append(k)
            ES.add(k)
            deg[v] += 1
            deg[u] += 1
            continue
        done = False
        for _ in range(60):
            idx = rng.randrange(len(E))
            p, q = E[idx]
            w = p if partner == 0 else q
            o = q if partner == 0 else p
            k = _key(v, w, color)
            if k in ES or o == v:
                continue
            ES.discard(E[idx])
            ES.add(k)
            E[idx] = k
            deg[o] -= 1
            deg[v] += 1
            done = True
            break
        if not done:
            break
    return deg[v]


def _anneal(n, edges, d, D, deadline, rng):
    """Anneal from a valid graph; return the largest valid (n, edges) reached, or None."""
    n0 = n
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = list(_bipartition(n, adj))
    E = [_key(u, v, color) for u, v in edges]
    ES = set(E)
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    cost = _count_bad(n, E, D)
    bound = lib.moore_bound(d, D)
    best = (n, list(E)) if cost == 0 else None

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        if cost == 0:
            best = (n, list(E))
            if n + 2 > bound:
                break
            # Attach a new point (side 0) and a new line (side 1).
            color.append(0)
            deg.append(0)
            x = n
            n += 1
            _attach(x, E, ES, deg, color, d, rng)
            color.append(1)
            deg.append(0)
            y = n
            n += 1
            _attach(y, E, ES, deg, color, d, rng)
            cost = _count_bad(n, E, D)
            continue

        # Saturate spare degree; this only adds edges, so cost cannot rise.
        f0 = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        f1 = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        pairs = [(a, b) for a in f0 for b in f1 if (a, b) not in ES]
        if pairs:
            rng.shuffle(pairs)
            for a, b in pairs:
                if deg[a] < d and deg[b] < d and (a, b) not in ES:
                    E.append((a, b))
                    ES.add((a, b))
                    deg[a] += 1
                    deg[b] += 1
            cost = _count_bad(n, E, D)
            continue

        m = len(E)
        if m < 2:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in ES or (c, b) in ES:
            continue

        frac = (time.monotonic() - t0) / span
        T = 0.6 * (1.0 - frac) + 0.03
        E[i] = (a, e)
        E[j] = (c, b)
        ES.discard((a, b))
        ES.discard((c, e))
        ES.add((a, e))
        ES.add((c, b))
        new = _count_bad(n, E, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            ES.discard((a, e))
            ES.discard((c, b))
            ES.add((a, b))
            ES.add((c, e))

    if best is not None and best[0] > n0:
        return best
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    p1 = start + 0.4 * total
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    bound = lib.moore_bound(d, D)

    # Phase 1: known constructions and their growth.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, p1, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            attempts = 0
            while time.monotonic() < p1 and attempts < 30:
                attempts += 1
                sub = random.Random(rng.randrange(1 << 30))
                n2, e2 = _grow(gq[0], gq[1], d, D, p1, sub)
                consider(n2, e2)

    if D >= 3 and best_n < bound:
        while time.monotonic() < p1 and best_n < bound:
            k = rng.choice([1, 2, 3, 4])
            G = max(best_n // (2 * k) + 1, 2)
            res = _group_search(d, D, k, G, rng, 200, p1)
            if res is not None:
                consider(res[0], res[1])

    # Phase 2: edge-switch annealing that grows the order from the best graph.
    if D >= 3 and d >= 3 and best_n < bound and time.monotonic() < deadline:
        res = _anneal(best_n, best[1], d, D, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
