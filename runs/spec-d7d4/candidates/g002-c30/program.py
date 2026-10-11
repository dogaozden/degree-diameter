import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
#   D = 3: incidence graph of PG(2, q), degree q + 1, diameter 3.
#   D >= 4: incidence graph of the generalized quadrangle W(q), degree q + 1,
#           order 2(q+1)(q^2+1), diameter 4. Every point of PG(3, q) is used,
#           since an alternating form makes every orthogonal pair totally isotropic.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Point-line incidence graph of W(q). Returns (n, edges), points 0..P-1, lines P..2P-1."""
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
    edges = []
    nl = 0
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
            for p in L:
                edges.append((p, P + nl))
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
            nl += 1
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Graph utilities on adjacency lists.
# ----------------------------------------------------------------------------

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
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side non-adjacent pairs in random order. Only adds edges,
    so distances can only shrink and diameter validity is preserved."""
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


# ----------------------------------------------------------------------------
# Cover-based growth.
#
# A new vertex v joined to a set C reaches w within D iff some c in C has
# dist(c, w) <= D - 1. So a valid addition is a cover of all vertices by
# radius-(D-1) balls of at most d vertices on one side. Existing distances only
# shrink, so the graph stays valid. Randomized greedy covers give diversity.
# ----------------------------------------------------------------------------

def _cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full:
        if len(chosen) >= d or not pool:
            return None
        gains = [((ball[s] & ~covered).bit_count(), s) for s in pool]
        best = max(gains)[0]
        if best <= 0:
            return None
        if randomize:
            thr = best if rng.random() < 0.6 else max(1, best - 1)
            opts = [s for g, s in gains if g >= thr]
            s = rng.choice(opts)
        else:
            s = max(gains)[1]
        pool.remove(s)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly add cover vertices. When stuck, saturate spare degree once and retry."""
    edges = list(edges)
    stuck_sat = False
    while time.monotonic() < deadline:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        color = _bipartition(n, adj)
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1

        sides = [0, 1]
        rng.shuffle(sides)
        chosen = None
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                break

        if not chosen:
            if stuck_sat:
                break
            edges = _saturate(n, edges, d, rng)
            stuck_sat = True
            continue

        stuck_sat = False
        v = n
        n += 1
        for s in chosen:
            edges.append((s, v))
    return n, edges


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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d < 2:
        return best

    # Base prime powers q with q + 1 <= d, largest first, capped for speed.
    qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:3]
    if not qs:
        return best

    cache = {}

    def base(q):
        if q not in cache:
            cache[q] = lib.projective_plane_incidence(q) if D == 3 else _gq_w(q)
        return cache[q]

    it = 0
    while time.monotonic() < deadline:
        q = qs[0] if (it % 2 == 0 or len(qs) == 1) else rng.choice(qs)
        it += 1
        n0, e0 = base(q)
        if time.monotonic() >= deadline:
            break
        e0 = _saturate(n0, e0, d, rng)
        consider(n0, e0)
        slice_end = min(deadline, time.monotonic() + 0.2 * time_limit)
        n2, e2 = _grow(n0, e0, d, D, slice_end, random.Random(rng.getrandbits(32)))
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
