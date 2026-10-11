import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Bold change: voltage lifts over a broader family of groups.
#
# The parent only used cyclic-by-cyclic semidirect products. Here we also use
# NON-cyclic abelian groups Z_a x Z_b, which give a different family of
# bi-Cayley-type lifts. Search is simulated annealing over voltages, where the
# cost counts unreached (representative, vertex) pairs plus duplicate darts.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g. Each A_i and B_j gets
# exactly d darts, so the lift is d-regular and bipartite.
# Left translation is an automorphism, so only 2k representatives need BFS.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _abelian(mods):
    """Return (order, perm) for Z_m1 x Z_m2 x ..., with perm(s) giving the list g -> g + s."""
    order = 1
    for m in mods:
        order *= m
    weights = []
    w = 1
    for m in mods:
        weights.append(w)
        w *= m
    digits = []
    for x in range(order):
        ds = []
        y = x
        for m in mods:
            ds.append(y % m)
            y //= m
        digits.append(ds)

    def perm(s):
        ds = digits[s]
        out = []
        for g in range(order):
            dg = digits[g]
            out.append(sum(((a + b) % m) * wt
                           for a, b, m, wt in zip(dg, ds, mods, weights)))
        return out

    return order, perm


def _sample_group(G, rng):
    """Return (order, perm) for a random group of order G, where perm(s) gives g -> g*s."""
    divs = [a for a in range(2, G) if G % a == 0 and G // a >= 2]
    kind = rng.random()
    if divs and kind < 0.6:
        a = rng.choice(divs)
        b = G // a
        if rng.random() < 0.5:
            a, b = b, a
        return _abelian([a, b])
    if kind < 0.8 or not divs:
        return _abelian([G])
    # Metacyclic semidirect product Z_m x| Z_k2.
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if m < 2 or k2 < 2:
            continue
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, (lambda s, mul=mul, order=order: [mul(g, s) for g in range(order)])
    return _abelian([G])


def _cost(k, G, D, darts, perms):
    """Duplicate darts plus unreached (representative, vertex) pairs. Zero means valid."""
    dup = len(darts) - len({(i, j, s) for i, j, s in darts})
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return dup * N * 4 + total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a sampled group of order about G.

    Returns (n, edges) with diameter <= D, or None.
    """
    if G < 2:
        return None
    G, permf = _sample_group(G, rng)
    cache = {}

    def getperm(s):
        if s not in cache:
            cache[s] = permf(s)
        return cache[s]

    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [getperm(s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        if new_s == old_s:
            continue
        darts[idx][2] = new_s
        perms[idx] = getperm(new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _edges(k, G, best_darts, best_perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed voltage lifts over abelian and metacyclic groups,
    # with 1-3 base vertices per side. Group orders target just above the best.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        res = _search(d, D, k, G, rng, 2000, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
