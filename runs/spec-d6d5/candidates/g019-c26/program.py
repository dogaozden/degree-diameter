import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (safe fallbacks): projective plane, Araujo-Pardo-Lopez,
# generalized quadrangle W(q), and cover/saturation growth.
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


def _gq_order(d):
    """Largest prime power q <= min(d - 1, 9), or None."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4.

    Points are 0..P-1, lines are P..2P-1; every edge joins a point to a line.
    """
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
    """Two-colouring of a graph given by adjacency lists or sets (proper if bipartite)."""
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
# New family: Z_m voltage lifts of the generalized quadrangle incidence graph.
#
# Base graph: incidence graph of W(q), bipartite, q+1 regular, diameter 4.
# Dart (u, v) with voltage a in Z_m joins (u, g) to (v, g + a) for every g.
# Lifts keep the degree, keep the bipartition (points vs lines), and have
# order base_n * m. The search anneals voltages to reach diameter <= D.
# ----------------------------------------------------------------------------

def _lift_cost(N, adj, D):
    """Ordered pairs at distance > D (bit-parallel). Zero iff diameter <= D and connected."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _set_dart(adj, u, v, m, old, new):
    """Move the m lifted edges of dart (u, v) from voltage old to voltage new."""
    for g in range(m):
        x = u * m + g
        yo = v * m + (g + old) % m
        yn = v * m + (g + new) % m
        adj[x].remove(yo)
        adj[yo].remove(x)
        adj[x].append(yn)
        adj[yn].append(x)


def _lift_edges(darts, volts, m):
    """Edge list of the lift for given darts and voltages."""
    E = []
    for (u, v), a in zip(darts, volts):
        for g in range(m):
            E.append((u * m + g, v * m + (g + a) % m))
    return E


def _anneal_lift(n0, darts, m, D, deadline, rng):
    """Simulated annealing over dart voltages in Z_m. Returns (best_voltages, best_cost)."""
    E = len(darts)
    N = n0 * m
    volts = [rng.randrange(m) for _ in range(E)]
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(darts, volts):
        for g in range(m):
            x = u * m + g
            y = v * m + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    cur = _lift_cost(N, adj, D)
    best_c, best_v = cur, volts[:]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 40.0, 0.5
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = T0 * (T1 / T0) ** frac
        e = rng.randrange(E)
        old = volts[e]
        new = (old + rng.randrange(1, m)) % m
        u, v = darts[e]
        _set_dart(adj, u, v, m, old, new)
        volts[e] = new
        c2 = _lift_cost(N, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            if cur < best_c:
                best_c, best_v = cur, volts[:]
        else:
            _set_dart(adj, u, v, m, new, old)
            volts[e] = old
    return best_v, best_c


# ----------------------------------------------------------------------------
# Haar graph fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.72 * time_limit     # voltage search ends here
    hard = start + 0.84 * time_limit    # repair/growth ends here
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    qq = _gq_order(d) if D >= 4 else None
    gq = _gq_w(qq) if qq is not None else None
    if gq is not None:
        consider(gq[0], gq[1])
        n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.14 * time_limit, rng)
        consider(n2, e2)

    # Main search for D >= 5 with d - 1 a prime power: voltage lifts of W(d-1).
    if D >= 5 and gq is not None and qq == d - 1:
        n0, darts = gq
        bound = 2 * sum((d - 1) ** i for i in range(D))
        ms = [m for m in range(2, 40) if n0 * m <= bound]
        near = None  # (cost, m, volts) of the best failed lift

        def attempt(m, dl):
            nonlocal near
            volts, c = _anneal_lift(n0, darts, m, D, dl, rng)
            if c == 0:
                consider(n0 * m, _lift_edges(darts, volts, m))
                return
            if near is None or c < near[0]:
                near = (c, m, volts)

        span = max(1e-3, end - time.monotonic())

        def slot(frac):
            return min(end, time.monotonic() + frac * span)

        # Cheap order first: m = 2 gives the old record-level 2 * base_n.
        for m, frac in [(2, 0.15), (3, 0.35)]:
            if m in ms and time.monotonic() < end - 0.5:
                attempt(m, slot(frac))

        # Remaining time: random restarts at larger lift orders.
        big = [m for m in ms if m >= 3]
        while big and time.monotonic() < end - 0.5:
            m = rng.choice(big)
            attempt(m, slot(0.12))

        # Repair the best near-miss by deleting far-off vertices, then saturate.
        if near is not None and time.monotonic() < hard - 0.5:
            c, m, volts = near
            E = _lift_edges(darts, volts, m)
            rep = _repair(n0 * m, E, D, hard, rng)
            if rep is not None:
                consider(rep[0], rep[1])
                e3 = _saturate_edges(rep[0], rep[1], d, rng)
                consider(rep[0], e3)
                if time.monotonic() < hard - 0.5:
                    n4, e4 = _grow(rep[0], e3, d, D,
                                   min(hard, time.monotonic() + 3.0), rng)
                    consider(n4, e4)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
