import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined search for bipartite graphs with max degree d and diameter D.
#
# 1. Arc-extended projective plane incidence graphs (diameter 3). Start from
#    PG(2, q) incidence. Choose SA (points, each line holds <= s of them) and SB
#    (lines, each point lies on <= s of them) independently, where s = d-q-1.
#    Add one A-vertex per SA point and one B-vertex per SB line.
#    Note: with q = 13, d = 16 the constraint forces |SA|, |SB| <= 14 (a
#    (k,2)-arc), so this family reaches exactly 2(q^2+q+1)+28 = 394 and
#    cannot exceed it by adding more PG-type vertices alone.
# 2. Greedy vertex insertion with ball-cover certificates. A new vertex joined
#    to N reaches every existing vertex within D if N covers all vertices within
#    distance D-1. Insertion never breaks validity.
# 3. Repair search. Remove a few edges, refill spare capacity with random cross
#    edges, try insertions, and keep the result only if lib.is_valid passes and
#    the order does not drop. This lets the search leave the arc family.
# 4. Annealed bi-Cayley voltage lifts for diameter >= 4 and as a late fallback.
#
# Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------


# ------------------------------- arc extensions ------------------------------

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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice: every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one A-vertex per SA point and one B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ------------------------------ ball utilities -------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _grow_adj(adj, color, d, D, rng, max_add):
    """Insert up to max_add covering vertices into adj (mutated). Returns (n, edges)."""
    R = D - 1
    added = 0
    while added < max_add:
        nn = len(adj)
        balls = _ball_masks(nn, adj, R)
        full = (1 << nn) - 1
        ok = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            cand = [u for u in range(nn) if color[u] == 1 - side and len(adj[u]) < d]
            if not cand:
                continue
            rng.shuffle(cand)
            covered = 0
            chosen = []
            pool = cand
            while covered != full and len(chosen) < d and pool:
                best_gain, bi = 0, -1
                for i, u in enumerate(pool):
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_gain, bi = g, i
                if bi < 0:
                    break
                u = pool[bi]
                chosen.append(u)
                covered |= balls[u]
                pool = pool[:bi] + pool[bi + 1:]
            if covered == full:
                w = nn
                adj.append(set())
                color.append(side)
                for u in chosen:
                    adj[u].add(w)
                    adj[w].add(u)
                ok = True
                break
        if not ok:
            break
        added += 1
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedy insertion with random spare cross-edge perturbations. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        n_before = len(adj)
        n_now, _ = _grow_adj(adj, color, d, D, rng, 1)
        if n_now > n_before:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(len(adj)) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(len(adj)) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _fill(adj, color, d, rng, tries):
    """Add random valid cross edges between spare vertices of opposite colours."""
    for _ in range(tries):
        A = [u for u in range(len(adj)) if color[u] == 0 and len(adj[u]) < d]
        B = [u for u in range(len(adj)) if color[u] == 1 and len(adj[u]) < d]
        if not A or not B:
            return
        u = rng.choice(A)
        v = rng.choice(B)
        if v not in adj[u]:
            adj[u].add(v)
            adj[v].add(u)


def _repair_search(n, edges, d, D, rng, deadline):
    """Remove a few edges, refill, grow, and accept only valid graphs with order not reduced."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        E = list(cur_e)
        for _ in range(rng.choice([1, 1, 2, 3])):
            if E:
                E.pop(rng.randrange(len(E)))
        adj = [set() for _ in range(cur_n)]
        for u, v in E:
            adj[u].add(v)
            adj[v].add(u)
        color = _side_colors(cur_n, adj)
        _fill(adj, color, d, rng, 6)
        n2, E2 = _grow_adj(adj, color, d, D, rng, 2)
        if n2 >= cur_n and lib.is_valid(n2, E2, d, D):
            cur_n, cur_e = n2, E2
            if n2 > best_n:
                best_n, best_e = n2, E2
    return best_n, best_e


# -------------------------- generalized quadrangle --------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------- voltage lifts --------------------------------

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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


# --------------------------------- build ------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    def at(frac):
        return start + frac * T

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

    # Already optimal (Moore bound): return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    # 1. Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        arcs = _arc_extensions(d, at(0.10), random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # 2. Greedy insertion on the best graph so far.
        if time.monotonic() < at(0.20):
            n2, e2 = _augment(best[0], best[1], d, D, rng, at(0.20))
            consider(n2, e2)

    if best_n >= lib.moore_bound(d, D):
        return best

    # Generalized quadrangle baseline for D >= 4.
    if D >= 4 and time.monotonic() < at(0.20):
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # 3. Repair search leaving the arc family.
    if time.monotonic() < at(0.70):
        n_r, e_r = _repair_search(best[0], best[1], d, D, rng, at(0.70))
        consider(n_r, e_r)

    # 4. Annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < at(0.82):
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, at(0.82), iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Final greedy insertion on the best graph.
    if D >= 2 and time.monotonic() < at(0.86):
        n_f, e_f = _augment(best[0], best[1], d, D, rng, at(0.90))
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
