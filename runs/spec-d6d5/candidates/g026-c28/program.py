import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (safe fallbacks): projective plane and arc extensions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Candidate (n, edges) graphs built from PG(2, q) plus arc vertices."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New family for D >= 4: bi-Cayley voltage lifts over semidirect products
# Z_m x| Z_k2, with k base vertices per side.
#
# Vertices: A_{i,g} = i*G + g,  B_{j,h} = (k+j)*G + h.
# Each of the d layers is a perfect matching between the k A-blocks and the
# k B-blocks; each dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g.
# Left multiplication by the group is an automorphism, so only the k A-block
# representatives and k B-block representatives need to be checked.
#
# Search: voltage-focused annealing where each move picks the best of several
# re-rolled voltages, plus B-matching swaps within a layer. The cost is the
# number of (representative, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12]
    for _ in range(100):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
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


def _make_perm(order, mul):
    """Cached map s -> [g -> mul(g, s)] over the group."""
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(order)]
            cache[s] = p
        return p

    return perm


def _cost(k, G, D, darts, perm, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D.

    Zero means valid. Returns early with a value above `limit` if exceeded.
    Duplicate darts (same i, j, s) give a huge cost.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = perm(s)
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + pm[g]
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


def _random_darts(d, k, G, rng):
    """d layers, each a random perfect matching of A-blocks to B-blocks, with random voltages."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _edges(k, G, darts, perm):
    E = set()
    for i, j, s in darts:
        pm = perm(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, perm, rng, deadline, iters):
    """Annealed search for a zero-cost voltage assignment. Returns darts or None."""
    darts = _random_darts(d, k, G, rng)
    cost = _cost(k, G, D, darts, perm)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())

        if k > 1 and rng.random() < 0.2:
            # Swap the B-endpoints of two darts in the same layer.
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perm, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        else:
            # Focused voltage move: try several re-rolls, keep the best.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            best_c, best_s = None, None
            for _ in range(6):
                s = rng.randrange(G)
                if s == old:
                    continue
                darts[idx][2] = s
                c = _cost(k, G, D, darts, perm,
                          limit if best_c is None else best_c)
                if best_c is None or c < best_c:
                    best_c, best_s = c, s
            if best_s is None:
                darts[idx][2] = old
                continue
            if best_c <= limit:
                darts[idx][2] = best_s
                cost = best_c
            else:
                darts[idx][2] = old

    return darts if cost == 0 else None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.15 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if best_n >= moore:
        return best

    # Main search: bi-Cayley voltage lifts over small semidirect products.
    if D >= 4:
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            if best_n >= moore:
                break
            k = rng.choice(ks)
            lo = max(2, best_n // (2 * k) + 1)
            hi = lo + max(2, lo // 8)
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            perm = _make_perm(order, mul)
            darts = _anneal(d, D, k, order, perm, rng, deadline, 800)
            if darts is not None:
                n, e = _edges(k, order, darts, perm)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
