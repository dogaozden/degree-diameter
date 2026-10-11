"""Bi-Cayley voltage-lift search for diameter-D bipartite graphs.

New in this version:
  * Translation normalization (k = 1): right-multiplying every voltage by a fixed
    group element relabels the B side and gives an isomorphic lift, so the first
    dart can be fixed to the identity. This shrinks the search space by a factor G.
  * Distinct initial voltages for k = 1, so the starting lift is simple.
  * Best-voltage scan move: for one dart, evaluate many candidate voltages and
    keep the best one (with Metropolis acceptance on the scanned optimum).
"""
import math
import random
import time

import lib

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


# ----------------------------------------------------------------------------
# Small classical families.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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

def _adj_lists(n, edges):
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]


def _repair(n, edges, D, deadline, rng):
    """Delete the most-offending vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = _adj_lists(cur_n, cur_e)
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


def _saturate_edges(n, edges, d, rng):
    """Greedily add opposite-colour edges between deficient vertices (only adds edges)."""
    edges = list(edges)
    adj = _adj_lists(n, edges)
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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Left multiplication by any h is an automorphism (associativity), so one
# representative per base vertex suffices for the diameter cost.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, pool):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(pool)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            return lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _random_darts(d, k, G, rng):
    """d layers; each layer is a random permutation of the k A-vertices onto the k B-vertices.
    For k = 1 the d voltages are distinct, so the initial lift is simple."""
    darts = []
    if k == 1:
        vs = rng.sample(range(G), d)
        return [[0, 0, s] for s in vs]
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(x[0], x[1], x[2]) for x in darts}) < len(darts):
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
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _scan_dart(k, G, D, darts, perms, mul, idx, rng, cost, limit, samples):
    """New move: evaluate many voltages for one dart and keep the best one.
    Accepts the scanned optimum if its cost is within `limit` (Metropolis threshold)."""
    old = darts[idx][2]
    old_perm = perms[idx]
    pool = range(G) if G <= samples else rng.sample(range(G), samples)
    best_c, best_s = None, None
    for s in pool:
        if s == old:
            continue
        darts[idx][2] = s
        perms[idx] = _right_perm(mul, G, s)
        lim = limit if best_c is None else best_c
        c = _cost(k, G, D, darts, perms, lim)
        if best_c is None or c < best_c:
            best_c, best_s = c, s
            if c == 0:
                break
    if best_c is not None and best_c <= limit:
        darts[idx][2] = best_s
        perms[idx] = _right_perm(mul, G, best_s)
        return best_c
    darts[idx][2] = old
    perms[idx] = old_perm
    return cost


def _anneal(d, D, k, G, mul, inv, rng, deadline, iters, start=None, T0=1.0):
    """Simulated annealing over voltages and B-assignments.

    Translation normalization (k = 1): right-multiply all voltages by inv(s_0), so
    dart 0 has voltage identity and is never moved; the lift is isomorphic.
    Returns (edges_or_None, darts, cost).
    """
    if start is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start]
    if k == 1:
        t = inv(darts[0][2])
        for x in darts:
            x[2] = mul(x[2], t)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    lo = 1 if k == 1 else 0
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        idx = rng.randrange(lo, len(darts))
        r = rng.random()
        if r < 0.35:
            cost = _scan_dart(k, G, D, darts, perms, mul, idx, rng, cost, limit, 24)
        elif r < 0.7 or k == 1:
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new
            perms[idx] = _right_perm(mul, G, new)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: annealed bi-Cayley lifts with translation normalization,
    # best-voltage scan moves, elite warm restarts, and repair of near misses.
    k2_pool = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    elite = {}
    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.7 else rng.choice([2, 3])
        lo = max(2, best[0] // (2 * k) + 1)
        hi = lo + max(3, lo // 4)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool)
        if g is None:
            continue
        order, mul, inv = g
        key = (k, order)

        start_darts, T0 = None, 1.0
        mul_use, inv_use = mul, inv
        if key in elite and rng.random() < 0.5:
            _, st, mul_use, inv_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1200 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul_use, inv_use, rng,
                                    deadline, iters, start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use, inv_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            out = _lift_repair(d, D, k, order, mul_use, darts_out,
                               min(deadline, time.monotonic() + 4.0), rng)
            if out is not None:
                consider(out[0], out[1])

    n, e = best[0], best[1]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
