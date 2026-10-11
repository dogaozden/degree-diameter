import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective planes (D = 3) and generalized quadrangles W(q) (D = 4).
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


# ----------------------------------------------------------------------------
# Shared utilities.
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices that are not yet adjacent (never raises diameter)."""
    edges = list(edges)
    adj = _adj_list(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Twin augmentation: a twin shares its neighbourhood, so distances are kept.
# ----------------------------------------------------------------------------

def _twin_augment(n, edges, d, rng, deadline):
    adj = _adj_list(n, edges)
    slack = [d - len(a) for a in adj]
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    best = []
    while cand:
        load = [0] * n
        chosen = []
        order = cand[:]
        rng.shuffle(order)
        for x in order:
            if all(load[w] < slack[w] for w in adj[x]):
                chosen.append(x)
                for w in adj[x]:
                    load[w] += 1
        if len(chosen) > len(best):
            best = chosen
        if time.monotonic() >= deadline:
            break
    E = list(edges)
    N = n
    for x in best:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Cover-based vertex addition: a new vertex joined to a set S of one side
# reaches everything if the radius-(D-1) balls of S cover all vertices.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mg = max(gains)
        if mg == 0:
            return None
        thr = mg - 1 if (randomize and rng.random() < 0.5) else mg
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _add_vertex(n, edges, d, D, rng):
    adj = _adj_list(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        for attempt in range(20):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                v = n
                E = list(edges)
                for s in chosen:
                    E.append((s, v))
                return n + 1, E
    return None


def _grow(n, edges, d, D, deadline, rng):
    while time.monotonic() < deadline:
        r = _add_vertex(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    return n, _saturate(n, edges, d, rng)


# ----------------------------------------------------------------------------
# NEW: pair splicing. Pick an edge (a, b), subdivide it into a-y-x-b and add
# the chord x-y. Both new vertices get degree 2 and are then topped up to d
# with edges to deficient opposite-side vertices. This adds two vertices while
# keeping all old degrees. The move is kept only if the result is valid.
# ----------------------------------------------------------------------------

def _splice(n, edges, d, D, rng):
    E = list(edges)
    adj = _adj_list(n, E)
    color = _bipartition(n, adj)
    ei = rng.randrange(len(E))
    a, b = E[ei]
    if color[a] == 1:
        a, b = b, a
    x, y = n, n + 1
    N = n + 2
    E[ei] = (a, y)
    E.append((x, b))
    E.append((x, y))
    deg = [0] * N
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    existing = {(min(u, v), max(u, v)) for u, v in E}
    for v, opp in ((x, 1), (y, 0)):
        cands = [w for w in range(n) if color[w] == opp and deg[w] < d]
        rng.shuffle(cands)
        for w in cands:
            if deg[v] >= d:
                break
            key = (min(v, w), max(v, w))
            if key in existing or deg[w] >= d:
                continue
            E.append((v, w))
            existing.add(key)
            deg[v] += 1
            deg[w] += 1
    if lib.is_valid(N, E, d, D):
        return N, E
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)
            main_end = start + 0.8 * time_limit
            while time.monotonic() < main_end and best_n < moore:
                tn, te = _twin_augment(best_n, best[1], d, rng,
                                       time.monotonic() + 0.02 * time_limit)
                consider(tn, te)
                gn, ge = _grow(tn, te, d, D, min(main_end, time.monotonic() + 0.03 * time_limit), rng)
                consider(gn, ge)

    if D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() > start + 0.4 * time_limit:
                break
            gn, ge = _gq_w(q)
            consider(gn, ge)
            tn, te = _twin_augment(gn, ge, d, rng, time.monotonic() + 0.03 * time_limit)
            consider(tn, te)
            gn2, ge2 = _grow(tn, te, d, D, time.monotonic() + 0.03 * time_limit, rng)
            consider(gn2, ge2)

        main_end = start + 0.88 * time_limit
        while time.monotonic() < main_end and best_n < moore:
            if rng.random() < 0.6:
                res = _splice(best_n, best[1], d, D, rng)
                if res is not None:
                    consider(res[0], res[1])
            else:
                tn, te = _twin_augment(best_n, best[1], d, rng,
                                       time.monotonic() + 0.01 * time_limit)
                gn, ge = _grow(tn, te, d, D, min(main_end, time.monotonic() + 0.02 * time_limit), rng)
                consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
