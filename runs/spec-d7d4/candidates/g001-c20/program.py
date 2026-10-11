import itertools
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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
    """Greedy set cover of `full` by at most d candidate vertices.

    With randomize=True, ties are broken at random and, fairly often, a
    slightly weaker candidate is taken, so repeated calls explore different covers.
    Returns the chosen list, or None if the cover fails.
    """
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (deterministic-ish growth, no repair).
# ----------------------------------------------------------------------------

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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree."""
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
# NEW: partial-cover insertion followed by simulated-annealing repair.
#
# A new vertex v is attached to d opposite-side vertices chosen by greedy
# partial coverage of their radius-(D-1) balls. When the cover is incomplete,
# the residual bad pairs are repaired by degree-preserving 2-switches and
# degree-moving rewires, minimizing the bad-pair count. Repair only adds or
# re-routes edges, so a fully repaired graph has max degree <= d and the same
# bipartition, and it is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _bad_count(n, nbset, D):
    """Number of unordered pairs at distance > D."""
    adj = [list(s) for s in nbset]
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(n, nbset, color, d, rng):
    """Join deficient opposite-side vertices greedily in random order (only adds edges)."""
    left = [v for v in range(n) if color[v] == 0 and len(nbset[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(nbset[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in nbset[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(nbset[a]) < d and len(nbset[b]) < d:
            nbset[a].add(b)
            nbset[b].add(a)


def _flip(nbset, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Inverse: _flip(nbset, a, e, c, b)."""
    nbset[a].discard(b); nbset[b].discard(a)
    nbset[c].discard(e); nbset[e].discard(c)
    nbset[a].add(e); nbset[e].add(a)
    nbset[c].add(b); nbset[b].add(c)


def _rewire(nbset, a, b, e):
    """Replace edge (a,b) by (a,e). Inverse: _rewire(nbset, a, e, b)."""
    nbset[a].discard(b); nbset[b].discard(a)
    nbset[a].add(e); nbset[e].add(a)


def _anneal(n, nbset, color, d, D, deadline, rng, T=0.7):
    """Simulated annealing on the bad-pair count. Returns True iff bad pairs reach 0."""
    elist = [[u, v] for u in range(n) if color[u] == 0 for v in nbset[u]]
    R = [v for v in range(n) if color[v] == 1]
    if not elist or not R:
        return False
    cur = _bad_count(n, nbset, D)
    while cur > 0 and time.monotonic() < deadline:
        if rng.random() < 0.75:
            i = rng.randrange(len(elist))
            j = rng.randrange(len(elist))
            a, b = elist[i]
            c, e = elist[j]
            if a == c or b == e or e in nbset[a] or b in nbset[c]:
                continue
            _flip(nbset, a, b, c, e)
            elist[i] = [a, e]
            elist[j] = [c, b]
            new = _bad_count(n, nbset, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _flip(nbset, a, e, c, b)
                elist[i] = [a, b]
                elist[j] = [c, e]
        else:
            i = rng.randrange(len(elist))
            a, b = elist[i]
            e = rng.choice(R)
            if e == b or e in nbset[a] or len(nbset[e]) >= d:
                continue
            _rewire(nbset, a, b, e)
            elist[i] = [a, e]
            new = _bad_count(n, nbset, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _rewire(nbset, a, e, b)
                elist[i] = [a, b]
    return cur == 0


def _insert_vertex(n, nbset, color, d, D, rng):
    """Add one vertex by partial greedy cover of radius-(D-1) balls. Returns new vertex count or None."""
    adj = [list(s) for s in nbset]
    ball = _balls_radius(n, adj, D - 1)
    c = rng.randrange(2)
    pool = [x for x in range(n) if color[x] == 1 - c]
    if len(pool) < d:
        return None
    covered = 0
    chosen = []
    for _ in range(d):
        bestk, bestx = -1.0, None
        for x in pool:
            g = (ball[x] & ~covered).bit_count()
            key = g + (0.5 if len(nbset[x]) < d else 0.0) + 0.4 * rng.random()
            if key > bestk:
                bestk, bestx = key, x
        pool.remove(bestx)
        chosen.append(bestx)
        covered |= ball[bestx]
    v = n
    color.append(c)
    nbset.append(set())
    for x in chosen:
        if len(nbset[x]) >= d:
            y = rng.choice(list(nbset[x]))
            nbset[x].discard(y)
            nbset[y].discard(x)
        nbset[x].add(v)
        nbset[v].add(x)
    return n + 1


def _anneal_grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert a vertex and repair by annealing; keep only valid growth.

    Returns the largest bad-pair-free graph found, starting from (n, edges).
    """
    nb = [set() for _ in range(n)]
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    color = _bipartition(n, [list(s) for s in nb])
    best = (n, nb, list(color))
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline:
        bn, bnb, bcol = best
        if bn >= moore:
            break
        cur_nb = [set(s) for s in bnb]
        col = list(bcol)
        m = _insert_vertex(bn, cur_nb, col, d, D, rng)
        if m is None:
            break
        _fill(m, cur_nb, col, d, rng)
        cap = min(deadline, time.monotonic() + 6.0)
        if _anneal(m, cur_nb, col, d, D, cap, rng):
            _fill(m, cur_nb, col, d, rng)
            best = (m, cur_nb, col)
    bn, bnb, bcol = best
    out = [(u, v) for u in range(bn) if bcol[u] == 0 for v in bnb[u]]
    return bn, out


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

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
# Haar and cyclic-lift families, kept as a secondary family.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    ext_deadline = start + 0.3 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
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

    # D >= 3: projective plane, grown by cover extension then saturation.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown likewise.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # NEW: partial-cover insertion with annealing repair, from the best graph so far.
    if D >= 3:
        n2, e2 = _anneal_grow(best_n, best[1], d, D, start + 0.8 * time_limit, rng)
        consider(n2, e2)

    # Secondary search: non-cyclic group lifts, Haar graphs and cyclic lifts.
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
