import math
import random
import time
import itertools

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group voltage lifts with a guided annealing search.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h, base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s.
#
# Left multiplication is an automorphism, so the lift has diameter <= D iff
# every class representative (identity of each of the 2k classes) reaches all
# vertices of the other class within D steps. Only those 2k BFS runs are needed.
#
# New idea in this version: "unreached-pair guided moves". When a representative
# misses a vertex of the opposite class, a dart from that class pair can be
# pointed straight at the missing vertex (voltage = its label, or its inverse
# for the B-side representative). This turns a missed pair into a direct edge,
# which is a far more informed move than a uniformly random voltage change.
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


def _column_table(G, mul):
    """T[s][g] = g * s, so right multiplication by s is the list T[s]."""
    return [[mul(g, s) for g in range(G)] for s in range(G)]


def _inverses(G, T):
    """inv[g] is the s with g * s = identity (identity is element 0)."""
    inv = [0] * G
    for s in range(G):
        row = T[s]
        for g in range(G):
            if row[g] == 0:
                inv[g] = s
    return inv


def _evaluate(k, G, D, darts, T):
    """Return (cost, misses). cost = unreached (rep, vertex) pairs; misses = cross-class unreached pairs."""
    keys = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in keys:
            return _BIG, []
        keys.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        col = T[s]
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + col[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    misses = []
    for ri in range(2 * k):
        src = ri * G
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
        lo, hi = (k * G, N) if ri < k else (0, k * G)
        for t in range(lo, hi):
            if not seen[t]:
                misses.append((ri, t))
    return total, misses


def _guided(k, G, darts, inv, misses, rng):
    """Propose (dart index, new voltage) that points a dart straight at a missed cross-class vertex."""
    ri, t = misses[rng.randrange(len(misses))]
    if ri < k:
        i = ri
        j = t // G - k
        s = t - (k + j) * G
    else:
        j = ri - k
        i = t // G
        s = inv[t % G]
    cands = [idx for idx, (a, b, _) in enumerate(darts) if a == i and b == j]
    if not cands:
        return None
    return rng.choice(cands), s


def _edges(k, G, darts, T):
    E = set()
    for i, j, s in darts:
        col = T[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + col[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, rng, budget_end):
    """Time-scheduled annealing over voltages. Returns (n, edges) with diameter <= D, or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    T = _column_table(G, mul)
    inv = _inverses(G, T)

    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    cost, misses = _evaluate(k, G, D, darts, T)

    best = cost
    best_darts = [list(x) for x in darts]
    t_start = time.monotonic()
    span = max(1e-3, budget_end - t_start)

    while best > 0:
        now = time.monotonic()
        if now >= budget_end:
            break
        frac = (now - t_start) / span
        temp = 2.0 * (1.0 - frac) + 0.05

        proposal = None
        if misses and rng.random() < 0.6:
            proposal = _guided(k, G, darts, inv, misses, rng)
        if proposal is None:
            idx = rng.randrange(len(darts))
            ns = rng.randrange(G)
        else:
            idx, ns = proposal

        old = darts[idx][2]
        if ns == old:
            continue
        darts[idx][2] = ns
        c2, m2 = _evaluate(k, G, D, darts, T)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, misses = c2, m2
            if cost < best:
                best = cost
                best_darts = [list(x) for x in darts]
        else:
            darts[idx][2] = old

    if best == 0:
        return _edges(k, G, best_darts, T)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_end = start + 0.78 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4 and time.monotonic() < search_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore bound stop immediately.
    moore = lib._moore_bound(d, D)

    while time.monotonic() < search_end and best_n < moore:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        if rng.random() < 0.5:
            offset = rng.choice([1, 2, 3])
        else:
            offset = rng.randrange(1, base // 4 + 2)
        G = max(2, base + offset)
        budget = min(search_end, time.monotonic() + 6.0)
        res = _anneal(d, D, k, G, rng, budget)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
