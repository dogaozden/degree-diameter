import itertools
import math
import random
import time

import numpy as np

import lib

# This program does its search in Python. The graph-diameter checks use numpy
# boolean reach matrices, which are fast enough for the lift annealing below.
# C_SOURCE is not used.


# ----------------------------------------------------------------------------
# Base construction: generalized quadrangle W(q) (degree q+1, diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q), order 2(q+1)(q^2+1)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg_qs(d, count=3):
    return [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:count]


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (used to grow base graphs).
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
            for attempt in range(100):
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
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
# NEW family: annealed voltage lifts over semidirect products Z_m x| Z_k,
# with a numpy reach-matrix cost (number of unordered pairs at distance > D).
# ----------------------------------------------------------------------------

def _bad_count_np(n, edges, D):
    """Number of unordered vertex pairs at distance more than D (numpy reach matrices)."""
    if n <= 1:
        return 0
    nb = [[] for _ in range(n)]
    for u, v in edges:
        nb[u].append(v)
        nb[v].append(u)
    w = max((len(a) for a in nb), default=1)
    w = max(w, 1)
    idx = np.empty((n, w), dtype=np.int64)
    for v in range(n):
        idx[v] = nb[v] + [v] * (w - len(nb[v]))  # pad with self (harmless in OR)
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        N = R.copy()
        for j in range(w):
            N |= R[idx[:, j]]
        if np.array_equal(N, R):
            break
        R = N
    return (n * n - int(R.sum())) // 2


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


def _anneal_lift(d, D, k, G, rng, deadline, max_iters):
    """Simulated annealing on dart voltages of a random d-regular bipartite k+k base.

    Returns (n, edges) with zero bad pairs, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [(i, k + p[i], rng.randrange(order)) for p in perms for i in range(k)]

    def evaluate(ds):
        n, e = lib.group_lift(2 * k, ds, order, mul)
        return n, e, _bad_count_np(n, e, D)

    n, e, c = evaluate(darts)
    T = 1.0
    it = 0
    while c > 0 and it < max_iters and time.monotonic() < deadline and order > 1:
        it += 1
        j = rng.randrange(len(darts))
        u, v, a = darts[j]
        na = rng.randrange(order)
        if na == a:
            continue
        darts[j] = (u, v, na)
        n2, e2, c2 = evaluate(darts)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(T, 1e-9)):
            n, e, c = n2, e2, c2
        else:
            darts[j] = (u, v, a)
        T = max(0.05, T * 0.995)
    return (n, e) if c == 0 else None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = best[0]
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Stage 1 (D >= 3): projective plane incidence graphs, grown by cover extension.
    if D >= 3:
        pg_qs = _best_pg_qs(d, 2)
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, start + 0.2 * time_limit - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # Stage 2 (D >= 4): generalized quadrangle W(q), grown by cover extension.
    if D >= 4 and best_n < bound:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.3 * time_limit, rng)
            consider(n2, e2)

    # Early exit when the Moore bound is already met (e.g. calibration d=3, D=3).
    if best_n >= bound:
        return best

    # Stage 3: annealed non-cyclic voltage lifts, aiming above the current best order.
    base_sizes = [2, 3, 4, 5, 6]
    while time.monotonic() < deadline and best_n < bound:
        k = rng.choice(base_sizes)
        floor = best_n // (2 * k) + 1
        G = max(floor, 2)
        G += rng.randrange(0, max(1, G // 20))
        res = _anneal_lift(d, D, k, G, rng, deadline, 400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
