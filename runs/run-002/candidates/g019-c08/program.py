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
# Group-voltage lifts over semidirect products, with a fast two-stage evaluator.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Left multiplication by any h is an automorphism, so each class A_i and B_j is
# one orbit. Hence the graph has diameter <= D iff, for each of the 2k base
# representatives, a BFS of depth D reaches every vertex.
#
# Search: simulated annealing over voltages.
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


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order G.

    Base: k A-vertices and k B-vertices, each A_i has exactly d darts (one per layer).
    Returns (n, edges) with diameter <= D, or None.
    """
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
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
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


# ----------------------------------------------------------------------------
# New idea: spare-degree augmentation.
#
# Many baselines (projective planes, quadrangles, lifts with slack) leave some
# vertices with degree < d. Two moves use that slack:
#
#  * Edge addition between opposite-colour vertices with spare degree. This
#    keeps the graph bipartite and degree-bounded, and can only shorten
#    distances, so it never breaks validity. It is applied in bulk and is cheap.
#  * Vertex addition: a new vertex joined to a few spare opposite-colour
#    vertices. This can break the diameter bound, so it is checked with
#    lib.is_valid and rolled back on failure.
#
# Edge additions are the way to create spare capacity for later vertex additions.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of a bipartite graph on 0..n-1."""
    adj = lib.adjacency(n, edges)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _augment(n, edges, d, D, rng, deadline):
    """Grow a valid graph by spare-degree edge and vertex additions. Returns (n, edges)."""
    col = _two_color(n, edges)
    adjset = [set() for _ in range(n)]
    cur_edges = []
    for u, v in edges:
        adjset[u].add(v)
        adjset[v].add(u)
        cur_edges.append((u, v))
    cur_n = n
    fails = 0

    while time.monotonic() < deadline and fails < 500:
        if rng.random() < 0.2:
            # Vertex addition, checked for validity.
            s = rng.randrange(2)
            spare = [v for v in range(cur_n) if col[v] != s and len(adjset[v]) < d]
            if not spare:
                fails += 1
                continue
            k = rng.randint(1, min(d, len(spare)))
            nb = rng.sample(spare, k)
            new_e = cur_edges + [(u, cur_n) for u in nb]
            if lib.is_valid(cur_n + 1, new_e, d, D):
                for u in nb:
                    adjset[u].add(cur_n)
                adjset.append(set(nb))
                col.append(s)
                cur_n += 1
                cur_edges = new_e
                fails = 0
            else:
                fails += 1
        else:
            # Edge addition: always keeps validity.
            spare = [v for v in range(cur_n) if len(adjset[v]) < d]
            if len(spare) < 2:
                fails += 1
                continue
            u = rng.choice(spare)
            opp = [v for v in spare if col[v] != col[u] and v not in adjset[u]]
            if not opp:
                fails += 1
                continue
            v = rng.choice(opp)
            adjset[u].add(v)
            adjset[v].add(u)
            cur_edges.append((u, v))
            fails = 0

    return cur_n, list(cur_edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Search gets most of the early budget. The augmentation phase runs later,
    # and a final margin is kept for validity checks and return.
    search_deadline = start + max(0.5, min(0.6 * time_limit, time_limit - 10.0))
    final_deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
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

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    while time.monotonic() < search_deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 1500, search_deadline)
        if res is not None:
            consider(res[0], res[1])

    # Spare-degree augmentation of the best graph found so far.
    if time.monotonic() < final_deadline:
        n2, e2 = _augment(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
