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
# Bi-Cayley / group-voltage lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Left multiplication by any h is an automorphism, so the diameter is <= D iff a
# depth-D BFS from each of the 2k base representatives reaches every vertex.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups_of_order(G, rng, cap=40):
    """All semidirect groups Z_m x| Z_k2 of order G (sampled up to `cap` r-values per k2)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:cap]:
            out.append((m, k2, r))
    return out


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG  # duplicate darts would waste degree
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _trial(d, D, k, G, rng, iters, deadline, groups):
    """One hill-climb run over voltages in a randomly chosen group of order G.

    Returns (n, edges) with diameter <= D, or None.
    """
    if not groups:
        return None
    m, k2, r = rng.choice(groups)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(order)])
    perms = [_right_perm(mul, order, s) for _, _, s in darts]
    cost = _cost(k, order, D, darts, perms)
    stall = 0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline or stall > 250:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(order)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, order, new_s)
        c2 = _cost(k, order, D, darts, perms)
        if c2 < cost:
            stall = 0
        else:
            stall += 1
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _edges(k, order, darts, perms)
    return None


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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: adaptive group-order climb.
    # next_G[k] is the group order to try next for base size k. It advances past
    # every successful order, so the search climbs upward through orders instead
    # of sampling a fixed window around the current best. Failed attempts are
    # retried with a small random offset so nearby orders still get explored.
    group_cache = {}

    def groups_for(G):
        if G not in group_cache:
            group_cache[G] = _groups_of_order(G, rng)
        return group_cache[G]

    next_G = {k: max(2, best_n // (2 * k) + 1) for k in (1, 2, 3)}

    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.75 else rng.choice([2, 3])
        G_lo = max(2, best_n // (2 * k) + 1)
        G = max(G_lo, next_G[k])
        if rng.random() < 0.5:
            G += rng.randrange(0, 6)

        res = _trial(d, D, k, G, rng, 800, deadline, groups_for(G))
        if res is not None:
            consider(res[0], res[1])
            next_G[k] = max(next_G[k], G + 1)
        else:
            next_G[k] = max(next_G[k], G_lo)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
