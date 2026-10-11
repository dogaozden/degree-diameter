import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs
# ----------------------------------------------------------------------------

def _largest_pp(maxq):
    """Largest prime power q with 2 <= q <= maxq, or None."""
    for q in range(maxq, 1, -1):
        if lib.is_prime_power(q):
            return q
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


# ----------------------------------------------------------------------------
# Cyclic voltage lifts of a bipartite base graph, searched by annealing.
# Cost = number of unreached (representative, vertex) pairs. By the translation
# symmetry of the Z_m lift, one representative per base vertex suffices.
# ----------------------------------------------------------------------------

def _lift_cost(bn, m, darts, D):
    N = bn * m
    adj = [[] for _ in range(N)]
    for u, v, a in darts:
        for g in range(m):
            x = u * m + g
            y = v * m + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    reach = [1 << x for x in range(N)]
    for _ in range(D):
        new = []
        for x in range(N):
            r = reach[x]
            for y in adj[x]:
                r |= reach[y]
            new.append(r)
        reach = new
    return sum(N - reach[u * m].bit_count() for u in range(bn))


def _search_lift(bn, be, m, D, rng, deadline, iters):
    """Anneal Z_m voltages on base edges be; return voltage list with zero cost, or None."""
    E = len(be)
    volt = [rng.randrange(m) for _ in range(E)]
    cost = _lift_cost(bn, m, [(u, v, volt[i]) for i, (u, v) in enumerate(be)], D)
    T = 3.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(E)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        c2 = _lift_cost(bn, m, [(u, v, volt[j]) for j, (u, v) in enumerate(be)], D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            volt[i] = old
        T = max(0.2, T * 0.998)
    return volt if cost == 0 else None


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover extension and edge saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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
# Entry point
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
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Plain projective plane (diameter 3) and generalized quadrangle (diameter 4), grown.
    q3 = _largest_pp(d - 1)
    if D >= 3 and q3 is not None:
        n, e = lib.projective_plane_incidence(q3)
        consider(n, e)
        gn, ge = _grow(n, e, d, D, min(deadline, time.monotonic() + 0.1 * time_limit), rng)
        consider(gn, ge)
    qg = _largest_pp(min(d - 1, 9))
    if D >= 4 and qg is not None:
        n, e = _gq_w(qg)
        consider(n, e)
        gn, ge = _grow(n, e, d, D, min(deadline, time.monotonic() + 0.1 * time_limit), rng)
        consider(gn, ge)

    # New family for the target (d=4, D=5): cyclic voltage lifts of the PG(2,3)
    # incidence graph (26 vertices) at large orders, and of the W(3) quadrangle
    # incidence graph (80 vertices) as a double cover, then diameter-preserving growth.
    if d == 4 and D == 5:
        pg_n, pg_e = lib.projective_plane_incidence(3)
        gq_n, gq_e = _gq_w(3)
        pending = [(pg_n, pg_e, 9), (pg_n, pg_e, 8), (pg_n, pg_e, 7),
                   (gq_n, gq_e, 2), (pg_n, pg_e, 6)]
        while pending and time.monotonic() < deadline:
            for item in list(pending):
                if time.monotonic() >= deadline:
                    break
                bn, be, m = item
                if bn * m < best_n:
                    pending.remove(item)
                    continue
                chunk_end = min(deadline, time.monotonic() + 2.5)
                volt = _search_lift(bn, be, m, D, rng, chunk_end, 3000)
                if volt is None:
                    continue
                darts = [(u, v, volt[i]) for i, (u, v) in enumerate(be)]
                n, e = lib.voltage_lift(bn, darts, m)
                consider(n, e)
                gn, ge = _grow(n, e, d, D, min(deadline, time.monotonic() + 8.0), rng)
                consider(gn, ge)
                pending.remove(item)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
