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
# New construction: twin extension of PG(2, q) using spare degree.
#
# Let d = q + 1 + s with s >= 1. Pick a set C of "centre" points and a set A of
# "axis" lines, with
#   - every line containing at most s centres,
#   - every point lying on at most s axes.
# Pair them up: for i < r = min(|C|, |A|) add
#   p_i (new point) adjacent to all q+1 lines through centre C[i], and to l_i;
#   l_i (new line) adjacent to all q+1 points on axis A[i], and to p_i.
# Degrees stay <= d. The extended graph has diameter 3:
#   p_i to old point x: a line through C[i] and x;
#   p_i to old line M: line L through C[i], meeting M in point x; path p_i-L-x-M;
#   l_i to old line M: via the point of A[i] that lies on M;
#   l_i to old point x: via a point of A[i] and the line joining it to x;
#   p_i, p_j share the line C[i]C[j]; l_i, l_j share a point of A[i] and A[j].
# This adds 2r vertices to the 2(q^2+q+1) of PG(2, q).
# ----------------------------------------------------------------------------

def _normalize(F, v):
    """Projective normalization: first nonzero coordinate becomes 1."""
    c = next(x for x in v if x)
    inv = F.inv(c)
    return tuple(F.mul(inv, x) for x in v)


def _select(num, elem_conts, n_conts, s, initial, rng, tries):
    """Pick elements so that each container receives at most s chosen elements.

    elem_conts[x] lists the containers of element x. Greedy with several orders,
    starting from the 'initial' elements (kept only when feasible).
    """
    best = []
    for t in range(tries):
        cnt = [0] * n_conts
        taken = [False] * num
        chosen = []
        order = list(initial)
        if t == 0:
            order += list(range(num))
        else:
            rest = list(range(num))
            rng.shuffle(rest)
            order += rest
        for x in order:
            if taken[x]:
                continue
            conts = elem_conts[x]
            if all(cnt[c] < s for c in conts):
                for c in conts:
                    cnt[c] += 1
                taken[x] = True
                chosen.append(x)
        if len(chosen) > len(best):
            best = chosen
    return best


def _twin_extension(q, d, rng):
    """PG(2, q) incidence plus r twin pairs using the s = d - (q+1) spare degree."""
    s = d - (q + 1)
    n0, edges0 = lib.projective_plane_incidence(q)
    m = n0 // 2
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}

    lines_of = [[] for _ in range(m)]   # point -> incident line indices
    pts_of = [[] for _ in range(m)]     # line -> incident point indices
    for u, v in edges0:
        lines_of[u].append(v - m)
        pts_of[v - m].append(u)

    centers_init, axes_init = [], []
    if q % 2 == 1:
        F = lib.GF(q)
        two = F.add(1, 1)
        conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
        dual = [(F.mul(t, t), F.neg(F.mul(two, t)), 1) for t in range(q)] + [(1, 0, 0)]
        centers_init = [index[_normalize(F, v)] for v in conic]
        axes_init = [index[_normalize(F, v)] for v in dual]

    C = _select(m, lines_of, m, s, centers_init, rng, 30)
    A = _select(m, pts_of, m, s, axes_init, rng, 30)
    r = min(len(C), len(A))

    n = 2 * m + 2 * r
    edges = list(edges0)
    for i in range(r):
        x = C[i]
        ax = A[i]
        p = 2 * m + i            # new point-side vertex
        l = 2 * m + r + i        # new line-side vertex
        for L in lines_of[x]:
            edges.append((p, m + L))
        for y in pts_of[ax]:
            edges.append((y, l))
        edges.append((p, l))
    return n, edges


def _best_twin(d, rng):
    """Best twin extension over the three largest prime powers q with q + 1 <= d."""
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
    best = None
    for q in qs:
        n, e = _twin_extension(q, d, rng)
        if best is None or n > best[0]:
            best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Group voltage lifts over semidirect products, with a fast two-stage evaluator.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Left multiplication by any h is an automorphism, so each class A_i and B_j is
# one orbit. Hence the graph has diameter <= D iff, for each of the 2k base
# representatives, a BFS of depth D reaches every vertex.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


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


def _search(d, D, k, G, rng, iters, deadline):
    """Hill-climb with occasional random acceptance over voltages in a group of order G."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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
        tw = _best_twin(d, rng)
        if tw is not None:
            consider(tw[0], tw[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: group voltage lifts with 1-3 base vertices per side.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 600, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
