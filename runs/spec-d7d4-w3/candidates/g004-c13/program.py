import itertools
import math
import random
import time

import lib

BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): incidence graph, diameter 4, degree q+1.
# ----------------------------------------------------------------------------

def _gq_w(q):
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


def _gq_base(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
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
    """Add edges between free left/right vertices. Keeps bipartiteness and only shortens distances."""
    edges = list(edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    adj = _adjacency(n, edges)
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
# Diameter-preserving growth by adding vertices whose radius-(D-1) balls cover.
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
        opts = [i for i, g in enumerate(gains) if g == best_g]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend(n, edges, d, D, deadline, rng):
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(12):
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
                placed = True
                break
        if not placed:
            break
    return n, edges


def _grow(g, d, D, deadline, rng):
    n, e = g
    e = _saturate(n, e, d, rng)
    n, e = _extend(n, e, d, D, deadline, rng)
    e = _saturate(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect groups Z_m x| Z_k, base k+k vertices, d layers.
# Cost = number of bad pairs, evaluated only from base representatives
# (valid because the group acts on the left and preserves every edge).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8])
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


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
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


def _edges_from(k, G, darts, mul):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + mul(g, s)))
    return sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = max(1.0, 0.05 * cost) if cost < BIG else 1.0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.3, T * 0.997)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            oldp = perms[idx]
            darts[idx][2] = new
            perms[idx] = [mul(g, new) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = oldp
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return 2 * k * G, _edges_from(k, G, darts, mul)
    return None


# ----------------------------------------------------------------------------
# Search drivers.
# ----------------------------------------------------------------------------

def _run_d3(d, consider):
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q >= 2:
        consider(*lib.projective_plane_incidence(q))
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass


def _run_big(d, D, seed, deadline, rng, consider, st):
    base = _gq_base(d)
    if base is None:
        return
    consider(*base)
    consider(*_grow(base, d, D, deadline, rng))
    lrng = random.Random(seed * 7919 + 101)
    while time.monotonic() < deadline and st["best"][0] < lib._moore_bound(d, D):
        cur = st["best"][0]
        k = lrng.randrange(1, 7)
        floor = cur // (2 * k) + 1
        G = floor + lrng.randrange(0, 3)
        g2 = _sample_group(G, lrng)
        if g2 is None:
            continue
        order, mul = g2
        lift = _search(d, D, k, order, mul, lrng, deadline, 1500)
        if lift is None:
            continue
        consider(*lift)
        consider(*_grow(lift, d, D, deadline, rng))


def _run(d, D, seed, deadline, rng, consider, st):
    if d <= 1 or D <= 2:
        return  # K_{d,d} fallback is already Moore-optimal for D = 2
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}
        return
    if D == 3:
        _run_d3(d, consider)
        return
    _run_big(d, D, seed, deadline, rng, consider, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    if st["best"][0] < lib._moore_bound(d, D):
        try:
            _run(d, D, seed, deadline, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
