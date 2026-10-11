import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), with decoupled sides.
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Old vertices have degree q+1, so each has spare capacity s = d - q - 1.
#
# A-side: a set SA of points. For each P in SA add a vertex x_P adjacent to
#   all q+1 lines through P. Load on each line L: #{P in SA : P on L} <= s.
# B-side: a set SB of line indices. For each j in SB add a vertex y_j adjacent
#   to all q+1 points on line j. Load on each point Q: #{j in SB : Q on j} <= s.
#
# The two sets are independent. Degrees stay <= d. Diameter stays 3: x_P and
# x_P' share line PP'; x_P reaches old points within 2 and old lines within 3;
# x_P and y_j are joined by a length-3 path through a line through P that meets
# j. Bipartiteness holds because x-vertices sit on the point side and y-vertices
# on the line side.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, pl, lp) for PG(2, q): pl[P] = lines through P, lp[L] = points on L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _is_arc(S, s, cover, m):
    """True if every element is covered by at most s centers of S."""
    load = [0] * m
    for c in S:
        for e in cover[c]:
            load[e] += 1
            if load[e] > s:
                return False
    return True


def _arc_search(m, s, cover, rng, deadline, init):
    """Find a large set of centers in range(m) with every element covered <= s times.

    Random greedy restarts, then plateau search with neutral swaps.
    """
    cover_sets = [set(c) for c in cover]
    best = list(init) if init and _is_arc(init, s, cover, m) else []
    order = list(range(m))
    for _ in range(25):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for c in order:
            if all(load[e] < s for e in cover[c]):
                S.append(c)
                for e in cover[c]:
                    load[e] += 1
        if len(S) > len(best):
            best = S

    S = list(best)
    inS = [False] * m
    load = [0] * m
    for c in S:
        inS[c] = True
        for e in cover[c]:
            load[e] += 1
    for _ in range(200000):
        if time.monotonic() > deadline:
            break
        c = rng.randrange(m)
        if inS[c]:
            continue
        over = [e for e in cover[c] if load[e] >= s]
        if not over:
            S.append(c)
            inS[c] = True
            for e in cover[c]:
                load[e] += 1
            if len(S) > len(best):
                best = list(S)
            continue
        blockers = [i for i, b in enumerate(S) if cover_sets[b].intersection(over)]
        if len(blockers) != 1:
            continue
        i = blockers[0]
        b = S[i]
        for e in cover[b]:
            load[e] -= 1
        if all(load[e] < s for e in cover[c]):
            S[i] = c
            inS[b] = False
            inS[c] = True
            for e in cover[c]:
                load[e] += 1
        else:
            for e in cover[b]:
                load[e] += 1
    return best


def _conic_set(q, index_of):
    """Conic (plus nucleus for even q) as a point index set, also valid as a dual arc of lines."""
    F = lib.GF(q)
    S = [index_of[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index_of[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index_of[(0, 1, 0)])
    return S


def _arc_graph_for_q(d, q, deadline, rng):
    """Build the decoupled arc-extension for PG(2, q) at degree d. Returns (n, edges) or None."""
    s = d - q - 1
    if s < 1:
        return None
    m, edges, pl, lp = _pg_data(q)
    init = []
    if s >= 2:
        pts = lib.projective_points(q)
        index_of = {p: i for i, p in enumerate(pts)}
        init = _conic_set(q, index_of)
    A = _arc_search(m, s, pl, rng, deadline, init)
    B = _arc_search(m, s, lp, rng, deadline, init)
    if not (_is_arc(A, s, pl, m) and _is_arc(B, s, lp, m)):
        return None
    n = 2 * m + len(A) + len(B)
    E = list(edges)
    for t, P in enumerate(A):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    off = 2 * m + len(A)
    for t, j in enumerate(B):
        y = off + t
        for Q in lp[j]:
            E.append((Q, y))
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts.
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


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


_BIG = 10 ** 9


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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

    # Decoupled arc-extended PG(2,q) graphs. Diameter 3, valid for all D >= 3.
    if D >= 3:
        qs = [q for q in range(2, min(d - 1, 23) + 1)
              if lib.is_prime_power(q) and d - q - 1 >= 1]
        arng = random.Random(seed * 7919 + d)
        for i, q in enumerate(qs):
            now = time.monotonic()
            slice_end = now + max(0.0, deadline - now) / (len(qs) - i)
            res = _arc_graph_for_q(d, q, slice_end, arng)
            if res is not None and res[0] > best_n:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
