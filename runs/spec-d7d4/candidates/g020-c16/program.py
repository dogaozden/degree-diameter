"""Bold variant for the D >= 4 targets: abandon twin blow-up and cover growth as
the main engine and search directly over voltage lifts (bi-Cayley graphs) with
k base vertices per side over a wide catalogue of finite groups: cyclic,
abelian products, affine groups AGL(1,p), and semidirect products Z_m x| Z_k.

Each candidate has order 2*k*|G| and is d-regular. Vertex-transitivity on each
side (left translation) means only k representatives per side need BFS, so the
cost is cheap. Threshold-accepting annealing minimises the number of
(representative, vertex) pairs at distance > D.

Safe fallbacks: K_{d,d} (diameter 2), the projective-plane incidence graph for
D = 3, and the generalized quadrangle W(q) incidence graph for D >= 4. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fixed bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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
# Finite groups of a prescribed order G, as (order, mul) with mul associative.
# ----------------------------------------------------------------------------

def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _group_options(G):
    """Descriptions of groups of order G that this module can build."""
    opts = [("cyc",)]
    for p in range(2, 40):
        if p * (p - 1) == G and _is_prime(p):
            opts.append(("aff", p))
    for a in range(2, G):
        if G % a == 0 and G // a >= 2:
            opts.append(("prod", a, G // a))
    for k2 in range(2, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append(("semi", m, k2, r))
    return opts


def _group_from(opt, G):
    """Return (G, mul) for a group option."""
    if opt[0] == "cyc":
        return G, (lambda x, y: (x + y) % G)
    if opt[0] == "aff":
        p = opt[1]

        def mul_aff(x, y):
            a, b = divmod(x, p)
            c, e = divmod(y, p)
            a += 1
            c += 1
            return ((a * c) % p - 1) * p + (a * e + b) % p

        return G, mul_aff
    if opt[0] == "prod":
        a, b = opt[1], opt[2]

        def mul_prod(x, y):
            x1, x2 = divmod(x, b)
            y1, y2 = divmod(y, b)
            return ((x1 + y1) % a) * b + (x2 + y2) % b

        return G, mul_prod
    _, m, k2, r = opt
    order, mul, _inv = lib.semidirect_group(m, k2, r)
    return order, mul


# ----------------------------------------------------------------------------
# Voltage lifts with k base vertices per side, d layers of matchings.
# Vertex (i, g) on side A and (k + j, g) on side B; a dart (i, j, s) joins
# (i, g) to (k + j, g*s) for all g. Each layer is a bijection, so the lift is
# d-regular. Left translations are automorphisms, so only k representatives per
# side need BFS.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Count (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Threshold-accepting search over voltages and layer target assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms, limit)
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
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(0.0, min(0.85 * T, T - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for every D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(res):
        nonlocal best
        if res is None:
            return
        n, e = res
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)

    # Algebraic bases.
    if D == 3:
        consider(_best_pg(d))
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= start + 0.2 * T:
                break
            consider(_gq_w(q))

    if best[0] >= moore:
        return best

    # Main engine: voltage-lift search with k base vertices per side.
    ks = [1, 2, 2, 3, 3, 4, 5, 6]
    slice_len = max(2.0, 0.08 * T)
    while time.monotonic() < deadline and best[0] < moore:
        feasible = [kk for kk in ks if best[0] // (2 * kk) + 1 <= moore // (2 * kk)]
        if not feasible:
            break
        k = rng.choice(feasible)
        lo = best[0] // (2 * k) + 1
        hi = moore // (2 * k)
        G = lo + rng.randrange(min(4, hi - lo + 1))
        opts = _group_options(G)
        if not opts:
            continue
        opt = rng.choice(opts)
        order, mul = _group_from(opt, G)
        slice_end = min(deadline, time.monotonic() + slice_len)
        res = _anneal(d, D, k, order, mul, rng, slice_end, iters=3000)
        consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
