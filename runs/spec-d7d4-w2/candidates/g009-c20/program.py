import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane incidence (D = 3) and generalized quadrangle W(q)
# incidence (D >= 4). Both are bipartite with diameter <= 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
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


def _balls(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
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


# ----------------------------------------------------------------------------
# Cover search: find <= d vertices on one side whose radius-(D-1) balls cover
# the whole graph. Such a vertex can be added while keeping diameter <= D.
# ----------------------------------------------------------------------------

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


def _exact_cover(cands, ball, full, d, budget):
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


def _insert(n, edges, d, D, rng):
    """Add one vertex whose neighbourhood covers everything within D-1. None if impossible."""
    adj = _adj_list(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        if D >= 4:
            chosen = _exact_cover(cands, ball, full, d, 300)
        if not chosen:
            for attempt in range(25):
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
        if chosen:
            v = n
            E = list(edges)
            E.extend((s, v) for s in chosen)
            return n + 1, E
    return None


def _saturate(n, edges, d, rng):
    """Add edges between deficient opposite-side vertices. Never increases any distance."""
    edges = list(edges)
    adj = _adj_list(n, edges)
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


def _fill(n, edges, d, D, rng, deadline):
    while time.monotonic() < deadline:
        r = _insert(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate(n, edges, d, rng)
    return n, edges


# ----------------------------------------------------------------------------
# Iterated local search: excise a random vertex, repair diameter, refill.
# Every accepted state is valid (diameter and degree preserved by each step).
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _ils(n, edges, d, D, deadline, rng, best):
    cn, ce = n, list(edges)
    bn, be = best
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re_ = _remove_vertex(cn, ce, x)
        if rn < 2:
            continue
        re_ = _saturate(rn, re_, d, rng)
        if not lib.within_diameter(rn, re_, D):
            continue
        rn, re_ = _fill(rn, re_, d, D, rng, deadline)
        if rn >= cn:
            cn, ce = rn, re_
            if rn > bn and lib.is_valid(rn, re_, d, D):
                bn, be = rn, re_
    return bn, be


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.85 * time_limit - 1.0)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Choose bases.
    bases = []
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
    else:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            bases.append(_gq_w(q))
    if not bases:
        bases.append(fallback)

    # Grow each base within its own share of the budget; keep the best state.
    states = []
    for idx, (n0, e0) in enumerate(bases):
        now = time.monotonic()
        if now >= deadline:
            break
        share_end = min(deadline, now + 0.25 * budget)
        seeded = _saturate(n0, e0, d, rng)
        n1, e1 = _fill(n0, seeded, d, D, rng, share_end)
        states.append((n1, e1))
        consider(n1, e1)

    if states:
        cur = max(states, key=lambda s: s[0])
    else:
        cur = best

    if best_n < moore and time.monotonic() < deadline:
        n2, e2 = _ils(cur[0], cur[1], d, D, deadline, rng, cur)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
