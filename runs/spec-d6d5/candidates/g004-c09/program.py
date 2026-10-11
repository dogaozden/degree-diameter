"""Bitset-annealed bi-Cayley voltage lifts over semidirect products (D >= 4 family),
with a fixed-size fallback chain: K_{d,d}, PG(2,q) incidence, W(q) incidence.

Each candidate lift has layered structure: d perfect matchings between k A-base and
k B-base vertices, with a group voltage on every dart. The annealing cost counts
(vertex, vertex) pairs at distance > D by bitset BFS over all N vertices, so it is
cheap enough to run thousands of moves per case. Every returned graph is checked
with lib.is_valid before it replaces the current best.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fixed bases (diameter 2, 3 and 4 respectively).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bitset cost: number of ordered (source, target) pairs at distance > D.
# ----------------------------------------------------------------------------

def _bits_cost(N, adj, D):
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _adj_from(k, G, darts, perms):
    """Adjacency lists of the layered lift. A_i,g = i*G+g, B_j,h = (k+j)*G+h."""
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
    return N, adj


def _cost(k, G, D, darts, perms):
    N, adj = _adj_from(k, G, darts, perms)
    return _bits_cost(N, adj, D)


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Group sampling and dart initialisation.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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


def _random_darts(d, k, G, rng):
    """d layers; each layer is a perfect matching i -> p[i] with a random voltage per dart."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


# ----------------------------------------------------------------------------
# Simulated annealing over voltages and layer matchings.
# ----------------------------------------------------------------------------

def _anneal(d, D, k, G, mul, rng, deadline, iters, darts):
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.1, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost, darts, perms


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D <= 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Main search: annealed layered voltage lifts over semidirect groups.
    ks = [1, 2, 2, 3, 4, 6] if D >= 5 else [1, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(4, base // 3 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        darts = _random_darts(d, k, order, rng)
        run_deadline = min(deadline, time.monotonic() + 6.0)
        cost, darts_out, perms = _anneal(d, D, k, order, mul, rng,
                                         run_deadline, 6000, darts)
        if cost == 0:
            n, e = _edges(k, order, darts_out, perms)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
