import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Classical families (kept as cheap, safe baselines for D = 3).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Generic graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline and cur_n > 0:
        adj = _adj(cur_n, cur_e)
        ball = _balls(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        order = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(order)
        order.sort(key=lambda v: -bad[v])
        batch = max(1, len(order) // 12)
        dead = set(order[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


def _saturate(n, edges, d, rng):
    """Add edges between deficient opposite-colour vertices (keeps bipartiteness and degree <= d)."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


# ----------------------------------------------------------------------------
# New family for D >= 5: bi-Cayley voltage lifts over semidirect products
# Z_m x| Z_k2, searched by a tabu-guided best-of-sample descent.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# Each layer of d layers is a permutation of the k A-classes onto the k B-classes,
# so every vertex has degree d.
# Left-multiplication by G is an automorphism, so the distance condition only needs
# to be checked from one representative per class (2k BFS runs).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0]
    for _ in range(60):
        k2 = rng.choice(divs)
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(300):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Tabu-guided descent over voltages and layer targets. Returns (best_cost, best_darts)."""
    darts = _random_darts(d, k, G, rng)
    perms = [_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    best_cost = cost
    best_darts = [list(x) for x in darts]
    tabu = {}
    stall = 0
    for it in range(1, iters + 1):
        if cost == 0 or time.monotonic() > deadline:
            break
        move_best = None
        c_best = None
        for _ in range(12):
            if k == 1 or rng.random() < 0.7:
                idx = rng.randrange(len(darts))
                s = rng.randrange(G)
                if s == darts[idx][2]:
                    continue
                key = ("v", idx)
                old_s, old_p = darts[idx][2], perms[idx]
                darts[idx][2] = s
                perms[idx] = _perm(mul, G, s)
                c = _cost(k, G, D, darts, perms)
                darts[idx][2] = old_s
                perms[idx] = old_p
                move = ("v", idx, s)
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                key = ("s", min(ia, ib), max(ia, ib))
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                c = _cost(k, G, D, darts, perms)
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                move = ("s", ia, ib)
            if tabu.get(key, 0) > it and c >= best_cost:
                continue
            if c_best is None or c < c_best:
                c_best = c
                move_best = (key, move)
        if move_best is None:
            continue
        key, mv = move_best
        if mv[0] == "v":
            darts[mv[1]][2] = mv[2]
            perms[mv[1]] = _perm(mul, G, mv[2])
        else:
            ia, ib = mv[1], mv[2]
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        cost = c_best
        tabu[key] = it + 7
        if cost < best_cost:
            best_cost = cost
            best_darts = [list(x) for x in darts]
            stall = 0
        else:
            stall += 1
            if stall > 150:
                break
    return best_cost, best_darts


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid whenever D >= 2.
    best = list(lib.haar_graph(d, range(d)))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # New search for D >= 5: bi-Cayley lifts over semidirect products.
    if D >= 5 and d >= 3:
        ks = [1, 2, 2, 3, 3, 4]
        while time.monotonic() < deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            lo = max(2, base + 1)
            hi = lo + max(3, lo // 6)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            c, darts = _search(d, D, k, order, mul, rng, deadline, 400)
            perms = [_perm(mul, order, s) for _, _, s in darts]
            n, e = _edges(k, order, darts, perms)
            if c == 0:
                consider(n, e)
            elif c <= 30 and time.monotonic() < deadline:
                rep = _repair(n, e, D, min(deadline, time.monotonic() + 3.0), rng)
                if rep is not None:
                    n2, e2 = rep
                    e2 = _saturate(n2, e2, d, rng)
                    consider(n2, e2)

    n_out, e_out = best[0], best[1]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, e_out
