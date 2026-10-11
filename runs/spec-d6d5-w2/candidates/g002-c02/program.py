import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families (safe fallbacks): projective plane, Araujo-Pardo-Lopez,
# generalized quadrangle W(q), and the trivial K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph utilities.
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices (only adds edges)."""
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


def _compact(n, edges, keep):
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, searched with a
# numpy-vectorised distance cost. Left translations act transitively on each
# side, so only one representative per side (2k in total) needs a BFS.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Each layer is a perfect matching between the A and B sides, so the
# maximum degree is exactly d.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices=None):
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _group_table(order, mul):
    """T[s, g] = g * s in the group."""
    T = np.zeros((order, order), dtype=np.int64)
    for s in range(order):
        for g in range(order):
            T[s, g] = mul(g, s)
    return T


def _lift_adj(k, G, darts, T):
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G)
    for i, j, s in darts:
        a = i * G + ar
        b = (k + j) * G + T[s]
        A[a, b] = 1.0
        A[b, a] = 1.0
    return A


def _cost_np(k, G, D, darts, T):
    """Total number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * k * G
    A = _lift_adj(k, G, darts, T)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = np.zeros((2 * k, N), dtype=np.float32)
    R[np.arange(2 * k), reps] = 1.0
    seen = R > 0
    frontier = R.copy()
    for _ in range(D):
        nxt = (frontier @ A) > 0
        nxt &= ~seen
        if not nxt.any():
            break
        seen |= nxt
        frontier = nxt.astype(np.float32)
    return int(2 * k * N - seen.sum())


def _edges_from(k, G, darts, T):
    E = set()
    for i, j, s in darts:
        row = T[s].tolist()
        for g in range(G):
            E.add((i * G + g, (k + j) * G + row[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Metropolis search over voltages and per-layer target permutations."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost_np(k, G, D, darts, T)
    temp = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp * 0.997)
        limit = cost - temp * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost_np(k, G, D, darts, T)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_np(k, G, D, darts, T)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Main search for D >= 5: vectorised bi-Cayley lifts over non-cyclic
        # groups, annealed on the exact distance cost, with repair of near misses.
        if D >= 5:
            k_choices = [1, 1, 2, 2, 3, 4, 5]
            k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
            while time.monotonic() < deadline:
                k = rng.choice(k_choices)
                base = best_n // (2 * k)
                lo = max(2, base + 1)
                hi = lo + max(3, lo // 8)
                G = rng.randint(lo, hi)
                g = None
                if rng.random() < 0.8:
                    g = _sample_group(G, rng, k2_pool)
                if g is None:
                    g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                T = _group_table(order, mul)

                darts, c = _anneal(d, D, k, order, T, rng, deadline, 1500)
                if c == 0:
                    n, e = _edges_from(k, order, darts, T)
                    consider(n, e)
                    continue

                # Near miss: delete far-off vertices, then saturate spare degree.
                if c <= 40 and rng.random() < 0.5 and time.monotonic() < deadline:
                    n, e = _edges_from(k, order, darts, T)
                    rep_deadline = min(deadline, time.monotonic() + 4.0)
                    rep = _repair(n, e, D, rep_deadline, rng)
                    if rep is not None:
                        n2, e2 = rep
                        e2 = _saturate_edges(n2, e2, d, rng)
                        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
