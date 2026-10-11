import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane and generalized quadrangle W(q).
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
# Cover-based growth: add vertices whose neighbourhoods cover everything
# within distance D-1, using spare degree on existing vertices.
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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
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
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products, annealed with a bitset
# cost. Base: k vertices per side, dl layers (perfect matchings), so every
# base vertex has degree dl. Dart (i, j, s) joins A_{i,g} to B_{j,g*s}.
# dl may be d-1, leaving spare degree for cover growth afterwards.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G (semidirect Z_m x| Z_k2, or cyclic)."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not opts:
        return None
    k2 = rng.choice(opts)
    m = G // k2
    if k2 == 1:
        order, mul, _ = lib.cyclic_group(m)
        return order, mul
    rs = [r for r in range(1, m)
          if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not rs:
        order, mul, _ = lib.cyclic_group(G)
        return order, mul
    r = rng.choice(rs)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    return order, mul


def _bad_ordered(N, adj, D):
    """Number of ordered vertex pairs at distance > D (unreachable counts). Zero iff valid."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _lift_adj(k, G, perm, darts):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = perm(s)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _lift_edges(k, G, perm, darts):
    E = set()
    for i, j, s in darts:
        pm = perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _accept(delta, T, rng):
    if delta <= 0:
        return True
    if delta > 50 * T:
        return False
    return rng.random() < math.exp(-delta / T)


def _anneal(dl, D, k, G, mul, rng, t_stop):
    """Simulated annealing over voltages and per-layer matchings. Returns (n, edges) or None."""
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    pl = []
    sv = []
    for _ in range(dl):
        p = list(range(k))
        rng.shuffle(p)
        pl.append(p)
        sv.append([rng.randrange(G) for _ in range(k)])

    def darts():
        return [(i, pl[L][i], sv[L][i]) for L in range(dl) for i in range(k)]

    def evaluate():
        ds = darts()
        if len(set(ds)) < len(ds):
            return _BIG
        n, adj = _lift_adj(k, G, perm, ds)
        return _bad_ordered(n, adj, D)

    cost = evaluate()
    t0 = time.monotonic()
    span = max(1e-3, t_stop - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= t_stop:
            break
        T = 3.0 * (0.03 ** ((now - t0) / span))
        if k == 1 or rng.random() < 0.6:
            L = rng.randrange(dl)
            i = rng.randrange(k)
            old = sv[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            sv[L][i] = new
            c2 = evaluate()
            if _accept(c2 - cost, T, rng):
                cost = c2
            else:
                sv[L][i] = old
        else:
            L = rng.randrange(dl)
            a, b = rng.sample(range(k), 2)
            p = pl[L]
            p[a], p[b] = p[b], p[a]
            c2 = evaluate()
            if _accept(c2 - cost, T, rng):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]
    if cost == 0:
        return _lift_edges(k, G, perm, darts())
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or d < 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # PG(2,q) with q + 1 = d is optimal; return instantly.
            if lib.is_prime_power(d - 1):
                return best
            n2, e2 = _grow(pg[0], pg[1], d, D,
                           min(deadline, time.monotonic() + 0.2 * (deadline - start)),
                           rng)
            consider(n2, e2)

    if D == 4:
        # Generalized quadrangle W(q) seeds with cover growth (short share of time).
        gq_end = min(deadline, time.monotonic() + 0.2 * (deadline - start))
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= gq_end:
                break
            n_g, e_g = _gq_w(q)
            consider(n_g, e_g)
            n2, e2 = _grow(n_g, e_g, d, D, gq_end, rng)
            consider(n2, e2)

    # Main phase: annealed lifts. Two modes:
    #  - grow mode: degree d-1 lift (spare slack), then cover growth;
    #  - plain mode: degree d lift, taken as is.
    ks = [2, 3, 4, 5, 6] if D >= 4 else [1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        grow_mode = d >= 3 and rng.random() < 0.6
        dl = d - 1 if grow_mode else d
        base = max(best[0], 120) if grow_mode else best[0] + 2
        G = max(2, base // (2 * k) + rng.randint(-1, 2))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        t_stop = min(deadline, time.monotonic() + rng.uniform(6.0, 14.0))
        res = _anneal(dl, D, k, order, mul, rng, t_stop)
        if res is None:
            continue
        n, e = res
        consider(n, e)
        if dl < d:
            n2, e2 = _grow(n, e, d, D, deadline, rng)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
