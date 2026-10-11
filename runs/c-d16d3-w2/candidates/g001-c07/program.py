import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Multiset-packed projective plane graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 each has spare capacity
# s = d - q - 1.
#
# A-side: for each point P choose a multiplicity a_P >= 0 and add a_P new
# vertices, each joined to the q+1 lines through P. Line L then gains
# sum_{P on L} a_P new neighbours, so we need that sum <= s.
# B-side: for each line j choose b_j >= 0 and add b_j new vertices, each
# joined to the q+1 points on j. Point Q gains sum_{j through Q} b_j <= s.
#
# Diameter stays 3 for any such choice: an A-vertex reaches every point via a
# line through its P, every line via a point of that line, and every B-vertex
# through a line through P meeting the B-line. The two sides are independent.
# Repeated points are allowed, so the capacity bound is about s*m/(q+1) per
# side. For d = 16, q = 13 this gives up to 26 per side, against the 14 that
# the old conic/arc construction managed (order 394), so the target is 418.
# The packing is found by simulated annealing with a removal-based move.
# Every candidate is still checked exactly with lib.is_valid.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _pack(cov, cov_items, s, rng, budget):
    """Maximise sum x_i (x_i >= 0 integers) subject to load[r] <= s for every resource r.

    cov[i] lists the resources used by item i. cov_items[r] lists the items using resource r.
    Returns the best multiplicity vector found within `budget` seconds.
    """
    m = len(cov)
    t0 = time.monotonic()
    x = [0] * m
    load = [0] * m
    total = 0
    best_total = 0
    best_x = [0] * m
    T = 0.6
    it = 0
    while True:
        it += 1
        if (it & 1023) == 0:
            frac = (time.monotonic() - t0) / budget
            if frac >= 1.0:
                break
            T = 0.05 + 0.55 * (1.0 - frac)
        i = rng.randrange(m)
        ci = cov[i]
        conflicts = [r for r in ci if load[r] >= s]
        if not conflicts:
            x[i] += 1
            for r in ci:
                load[r] += 1
            total += 1
        else:
            removal = []
            ok = True
            for r in conflicts:
                if load[r] < s:
                    continue
                cands = [j for j in cov_items[r] if x[j] > 0 and j != i]
                if not cands:
                    ok = False
                    break
                j = rng.choice(cands)
                x[j] -= 1
                for rr in cov[j]:
                    load[rr] -= 1
                removal.append(j)
            if ok:
                delta = 1 - len(removal)
                if delta >= 0 or rng.random() < math.exp(delta / T):
                    x[i] += 1
                    for r in ci:
                        load[r] += 1
                    total += delta
                    removal = None
            if removal is not None:
                for j in removal:
                    x[j] += 1
                    for rr in cov[j]:
                        load[rr] += 1
        if total > best_total:
            best_total = total
            best_x = list(x)
    return best_x


def _packed_graph(m, edges, point_lines, line_points, xa, xb):
    """Old PG incidence plus xa[P] A-vertices per point P and xb[j] B-vertices per line j."""
    E = list(edges)
    n = 2 * m
    for P in range(m):
        for _ in range(xa[P]):
            x = n
            n += 1
            for L in point_lines[P]:
                E.append((x, m + L))
    for j in range(m):
        for _ in range(xb[j]):
            y = n
            n += 1
            for Q in line_points[j]:
                E.append((Q, y))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    if not qs:
        return out
    remaining = max(0.5, deadline - time.monotonic())
    per_side = max(0.2, remaining / (2.0 * len(qs)))
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_data(q)
        if s >= 1:
            # A-side: items are points, resources are lines.
            # Resource L is used by points on L, which is line_points[L].
            xa = _pack(point_lines, line_points, s, rng, per_side)
            # B-side: items are lines, resources are points.
            # Resource Q is used by lines through Q, which is point_lines[Q].
            xb = _pack(line_points, point_lines, s, rng, per_side)
        else:
            xa = [0] * m
            xb = [0] * m
        n_c, e_c = _packed_graph(m, edges, point_lines, line_points, xa, xb)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3).
#
# A new vertex x on one side of a bipartite graph is at distance 2 from every
# vertex of its own side only if its neighbourhood T (on the other side) covers
# that whole side. So we greedily pick T among opposite-side vertices with spare
# degree, and accept x only if the whole graph still passes lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
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


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    """Permutation g -> mul(g, s) of the group."""
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

    # Multiset-packed projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Greedily fill spare degree with extra cover-type vertices (diameter 3).
    if D >= 3 and best_n > 2:
        fill_deadline = start + 0.6 * time_limit
        n_f, e_f = _fill(best_n, best[1], d, D, fill_deadline,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

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
