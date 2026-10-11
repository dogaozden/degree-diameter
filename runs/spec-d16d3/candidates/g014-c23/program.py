import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (D = 3): arc-extended projective plane incidence graphs.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Add a new point-side vertex for each P in S (joined to the q+1 lines through P)
# and a new line-side vertex for each j in S (joined to the q+1 points on j).
# This is valid when every line holds <= s points of S and every point lies on
# <= s lines of S, where s = d - q - 1. For d = 16, q = 13 the conic is an arc
# of size 14, giving the 394-vertex parent graph.
#
# Stage 2 (D = 3): augmentation search. Starting from the best valid stage-1
# graph, add one new vertex at a time and try to repair it with degree-bounded
# rewiring (edge add / remove / bipartite double-edge swap). Simulated annealing
# minimises the number of vertex pairs at distance > D. Each round is kept only
# if it reaches zero bad pairs, so the output is always a verified graph.
#
# Note: for pencil-type extensions the arc bound caps q = 13 at 394, so any gain
# must come from rewiring, which this search attempts. If it fails, the
# verified 394 graph is returned.
#
# Stage 3 (D >= 4): generalized quadrangle / voltage-lift search from the parent.
# ----------------------------------------------------------------------------


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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new point-side and a new line-side vertex per element of S."""
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


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges, side) for each prime power q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        side = [0] * m + [1] * m + [0] * len(S) + [1] * len(S)
        out.append((n_c, e_c, side))
    return out


# ----------------------------------------------------------------------------
# Stage 2: augmentation search (D = 3).
# ----------------------------------------------------------------------------

def _bad(n, nb, D):
    """Number of ordered vertex pairs at distance > D (0 means valid diameter)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _search(nb, side, n, d, D, deadline, rng, max_iters=4000):
    """Anneal degree-bounded bipartite rewiring until the diameter is <= D. Return nb or None."""
    cur = _bad(n, nb, D)
    if cur == 0:
        return nb
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    T = 2.0
    for _ in range(max_iters):
        if time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.999)
        r = rng.random()
        if r < 0.35:
            cand0 = [v for v in side0 if len(nb[v]) < d]
            cand1 = [v for v in side1 if len(nb[v]) < d]
            if not cand0 or not cand1:
                continue
            x = rng.choice(cand0)
            y = rng.choice(cand1)
            if y in nb[x]:
                continue
            nb[x].add(y)
            nb[y].add(x)
            c2 = _bad(n, nb, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                nb[x].discard(y)
                nb[y].discard(x)
        elif r < 0.5:
            x = rng.choice(side0)
            if not nb[x]:
                continue
            y = rng.choice(list(nb[x]))
            nb[x].discard(y)
            nb[y].discard(x)
            c2 = _bad(n, nb, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                nb[x].add(y)
                nb[y].add(x)
        else:
            x1 = rng.choice(side0)
            x2 = rng.choice(side0)
            if not nb[x1] or not nb[x2]:
                continue
            y1 = rng.choice(list(nb[x1]))
            y2 = rng.choice(list(nb[x2]))
            if x1 == x2 or y1 == y2 or y2 in nb[x1] or y1 in nb[x2]:
                continue
            # Degree-preserving double-edge swap.
            nb[x1].discard(y1); nb[y1].discard(x1)
            nb[x2].discard(y2); nb[y2].discard(x2)
            nb[x1].add(y2); nb[y2].add(x1)
            nb[x2].add(y1); nb[y1].add(x2)
            c2 = _bad(n, nb, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                nb[x1].discard(y2); nb[y2].discard(x1)
                nb[x2].discard(y1); nb[y1].discard(x2)
                nb[x1].add(y1); nb[y1].add(x1)
                nb[x2].add(y2); nb[y2].add(x2)
        if cur == 0:
            return nb
    return nb if cur == 0 else None


def _augment(n0, E0, side0, d, D, deadline, rng):
    """Repeatedly add one vertex and repair it. Returns the largest verified (n, edges)."""
    n, E, side = n0, list(E0), list(side0)
    while time.monotonic() < deadline:
        nb = [set() for _ in range(n + 1)]
        for u, v in E:
            nb[u].add(v)
            nb[v].add(u)
        x = n
        side_ext = side + [0]
        ys = [v for v in range(n) if side[v] == 1 and len(nb[v]) < d]
        rng.shuffle(ys)
        for y in ys[:d]:
            nb[x].add(y)
            nb[y].add(x)
        res = _search(nb, side_ext, n + 1, d, D, deadline, rng)
        if res is None:
            break
        n += 1
        side = side_ext
        E = [(u, v) for u in range(n) for v in res[u] if u < v]
    return n, E


# ----------------------------------------------------------------------------
# Stage 3 (D >= 4): generalized quadrangle and annealed voltage lifts (from parent).
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


def _vcost(k, G, D, darts, perms):
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


def _vedges(k, G, darts, perms):
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
    cost = _vcost(k, G, D, darts, perms)

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
            c2 = _vcost(k, G, D, darts, perms)
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
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if time_limit > 10:
        budget = min(0.8 * time_limit, time_limit - 5.0)
    else:
        budget = 0.5 * time_limit
    budget = max(0.5, budget)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Stage 1: arc-extended projective plane graphs (valid for D = 3).
        arc_deadline = start + 0.15 * budget
        cands = _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        seed_graph = None
        for n_c, e_c, side_c in cands:
            if lib.is_valid(n_c, e_c, d, D):
                consider(n_c, e_c)
                if seed_graph is None:
                    seed_graph = (n_c, e_c, side_c)
                break
        # Stage 2: augmentation search from the best verified arc graph.
        if seed_graph is not None and time.monotonic() < deadline:
            n_a, e_a, side_a = seed_graph
            n_f, e_f = _augment(n_a, e_a, side_a, d, D, deadline, rng)
            consider(n_f, e_f)
    else:
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
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
