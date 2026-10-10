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
# Group voltage lift search (parent family).
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
    """Hill-climb over voltages in a group of order G. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# New helper: spare-degree greedy extension.
#
# Given a valid bipartite graph, two moves keep it valid:
#   (A) add an edge between spare vertices on opposite sides. Distances only
#       shrink, so validity is preserved without any check.
#   (B) add a new vertex w on side X, joined to a set S of spare vertices on
#       the opposite side. Distance from w to any vertex x is 1 + min_s d(s, x),
#       so w is within D of everything iff the radius-(D-1) balls of S cover
#       all old vertices. This is a set-cover test, done with bitmasks.
#
# Balls are computed on the graph before this round's edges. Those balls are
# subsets of the true balls, so the test is conservative and stays sound.
# ----------------------------------------------------------------------------

def _coloring(n, adjl):
    """Proper 2-colouring of a bipartite graph (components started at 0)."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adjl[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _radius_balls(n, adjl, R):
    """Bitmask of the ball of radius R around each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjl[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _greedy_cover(cands, R, full, d, rng):
    """Pick at most d candidates whose balls cover `full`; return the list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_gain, best_i = 0, -1
        for i, c in enumerate(pool):
            gain = (R[c] & ~covered).bit_count()
            if gain > best_gain:
                best_gain, best_i = gain, i
        if best_i < 0:
            break
        c = pool.pop(best_i)
        chosen.append(c)
        covered |= R[c]
    return chosen if covered == full else None


def _extend(n, edges, d, D, rng, deadline):
    """Grow a valid bipartite graph by free edges and conservative vertex insertions."""
    E = [tuple(e) for e in edges]
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)

    while time.monotonic() < deadline:
        N = len(adj)
        adjl = [list(s) for s in adj]
        full = (1 << N) - 1
        col = _coloring(N, adjl)
        R = _radius_balls(N, adjl, D - 1)

        # Move (A): free edges between spare vertices on opposite sides.
        spare0 = [v for v in range(N) if col[v] == 0 and len(adj[v]) < d]
        spare1 = [v for v in range(N) if col[v] == 1 and len(adj[v]) < d]
        rng.shuffle(spare0)
        rng.shuffle(spare1)
        added = False
        for u in spare0:
            if len(adj[u]) >= d:
                continue
            for v in spare1:
                if len(adj[v]) < d and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    E.append((u, v))
                    added = True
                    if len(adj[u]) >= d:
                        break
        if added:
            continue  # refresh balls before trying insertions

        # Move (B): insert a new vertex by covering all vertices with spare neighbours.
        inserted = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            cands = [v for v in range(N) if col[v] == side and len(adj[v]) < d]
            for _ in range(3):
                chosen = _greedy_cover(cands, R, full, d, rng)
                if chosen is not None:
                    w = N
                    adj.append(set(chosen))
                    for c in chosen:
                        adj[c].add(w)
                        E.append((c, w))
                    inserted = True
                    break
            if inserted:
                break
        if not inserted:
            break

    return len(adj), E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_deadline = start + 0.5 * time_limit
    ext_deadline = start + 0.8 * time_limit
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

    # Main search: group voltage lifts with 1-3 base vertices per side.
    while time.monotonic() < search_deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _search(d, D, k, G, rng, 600, search_deadline)
        if res is not None:
            consider(res[0], res[1])

    # New: spare-degree greedy extension of the best graph found so far.
    if D >= 2 and time.monotonic() < ext_deadline:
        en, ee = _extend(best_n, best[1], d, D, rng, ext_deadline)
        if en > best_n:
            consider(en, ee)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
