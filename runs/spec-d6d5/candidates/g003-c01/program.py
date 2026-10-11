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


def _moore_bipartite(d, D):
    """Bipartite Moore bound 2 * sum_{i<D} (d-1)^i for d >= 3."""
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Bi-Cayley / group-voltage search.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g in the group.
# Left multiplication is an automorphism, so each block is one orbit and it is
# enough to BFS from one representative per block (2k BFS runs).
#
# Groups: semidirect products Z_m x| Z_k2 (r = 1 gives the abelian direct
# product, so both abelian and non-abelian groups are covered).
# Search: simulated annealing over voltages, with a ladder of target orders
# that rises each time a valid lift is found.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in _divisors(G) if G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs[:12]:
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [1]
            pool = rng.sample(range(1, m), min(m - 1, 200))
            for rr in pool:
                if math.gcd(rr, m) == 1 and pow(rr, k2, m) == 1 % m:
                    cands.append(rr)
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _has_conflict(darts):
    """True if two darts coincide, which would create duplicate edges."""
    seen = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return True
        seen.add(key)
    return False


def _unreached(adj, N, src, D):
    """Number of vertices not within distance D of src."""
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
    return N - count


def _cost(k, G, D, darts, perm):
    """Total unreached (representative, vertex) pairs. Zero means diameter <= D."""
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
    total = 0
    for blk in range(2 * k):
        total += _unreached(adj, N, blk * G, D)
    return total


def _edges(k, G, darts, perm):
    E = set()
    for i, j, s in darts:
        pm = perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, iters, deadline):
    """Simulated annealing over voltages. Returns (n, edges) with diameter <= D, or None."""
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    # Layers: each layer is a permutation, so every A_i and every B_j gets d darts.
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    for _ in range(300):
        if not _has_conflict(darts):
            break
        idx = rng.randrange(len(darts))
        darts[idx][2] = rng.randrange(G)
    if _has_conflict(darts):
        return None

    cost = _cost(k, G, D, darts, perm)
    best_cost = cost
    best_darts = [list(x) for x in darts]

    T0 = 2.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.1
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        new = rng.randrange(G)
        if new == old:
            continue
        darts[idx][2] = new
        if _has_conflict(darts):
            darts[idx][2] = old
            continue
        c2 = _cost(k, G, D, darts, perm)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
        else:
            darts[idx][2] = old

    if best_cost != 0:
        return None
    return _edges(k, G, best_darts, perm)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 8.0)
    deadline = start + max(0.5, budget)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D. Optimal for d = 2.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

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

    # Stop early if the fallback already meets the bipartite Moore bound.
    if d >= 3 and best_n >= _moore_bipartite(d, D):
        return best

    rng = random.Random(seed)
    while time.monotonic() < deadline:
        if deadline - time.monotonic() < 0.5:
            break
        k = rng.choice([1, 1, 1, 2])
        # Need 2*k*G > best_n to improve; aim just above the current best.
        need = best_n // (2 * k) + 1
        G = need + rng.randrange(0, max(2, need // 25 + 1))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, 2500, deadline)
        if res is not None:
            consider(res[0], res[1])
        if d >= 3 and best_n >= _moore_bipartite(d, D):
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
