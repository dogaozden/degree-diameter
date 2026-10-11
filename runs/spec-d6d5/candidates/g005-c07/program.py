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
# New in this version: a group catalogue and bitset diameter evaluator.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group. Left
# multiplication is an automorphism, so each A_i and each B_j is one orbit;
# the lift has diameter <= D iff a depth-D search from each of the 2k base
# representatives reaches every vertex.
#
# Two moves keep every A and B vertex at degree exactly d:
#   * change the voltage s of one dart;
#   * swap the B-endpoints j of two darts in the same layer.
# The cost is evaluated with Python-int bitsets (one OR per frontier vertex),
# which is much faster than list-based BFS for these graph sizes.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _bits(m):
    """Yield the indices of the set bits of integer m."""
    while m:
        low = m & -m
        yield low.bit_length() - 1
        m ^= low


def _group_catalogue(G):
    """All semidirect products Z_m x| Z_k2 of order G with k2 <= 12, as (m, k2, r) triples."""
    out = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _nbr_masks(k, G, darts, perm_of):
    """Neighbour bitmask for every vertex of the lift."""
    N = 2 * k * G
    nb = [0] * N
    for i, j, s in darts:
        pm = perm_of(s)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            nb[a] |= 1 << b
            nb[b] |= 1 << a
    return nb


def _bitset_cost(k, G, D, nb):
    """Total number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = 1 << src
        frontier = seen
        for _ in range(D):
            acc = 0
            for u in _bits(frontier):
                acc |= nb[u]
            new = acc & ~seen
            if not new:
                break
            seen |= new
            frontier = new
        total += N - seen.bit_count()
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealing over voltages and B-endpoints. Returns (n, edges) with diameter <= D, or None."""
    perm_cache = {}

    def perm_of(s):
        if s not in perm_cache:
            perm_cache[s] = [mul(g, s) for g in range(G)]
        return perm_cache[s]

    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    def cost_of(ds):
        if len({tuple(x) for x in ds}) < len(ds):
            return _BIG
        return _bitset_cost(k, G, D, _nbr_masks(k, G, ds, perm_of))

    cur = cost_of(darts)
    best = cur
    best_state = [list(x) for x in darts]
    T0 = 2.0
    for t in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        if k > 1 and rng.random() < 0.35:
            layer = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            a = darts[layer * k + i1]
            b = darts[layer * k + i2]
            a[1], b[1] = b[1], a[1]
            c2 = cost_of(darts)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                a[1], b[1] = b[1], a[1]
                continue
        else:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2 = cost_of(darts)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[idx][2] = old
                continue
        if cur < best:
            best = cur
            best_state = [list(x) for x in darts]

    if best != 0:
        return None
    E = set()
    for i, j, s in best_state:
        pm = perm_of(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Main search: annealed lifts over catalogued semidirect groups,
    # with 1-3 base vertices per side. Target orders just above the best so far.
    catalogue_cache = {}
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 4 + 1)))
        if G not in catalogue_cache:
            catalogue_cache[G] = _group_catalogue(G)
        cat = catalogue_cache[G]
        if not cat:
            continue
        m, k2, r = rng.choice(cat)
        _, mul, _ = lib.semidirect_group(m, k2, r)
        budget = min(deadline, time.monotonic() + 6.0)
        res = _anneal(d, D, k, G, mul, rng, budget, iters=4000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
