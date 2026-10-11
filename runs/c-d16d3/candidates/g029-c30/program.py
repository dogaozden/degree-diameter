import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base with INDEPENDENT dual arcs.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so spare capacity s = d - q - 1 remains.
#   * A-vertices x_P (P in S_A) join the q+1 lines through P. A line may gain
#     at most s such neighbours, so every line meets S_A in <= s points.
#   * B-vertices y_j (j in S_B) join the q+1 points on line j. A point may gain
#     at most s such neighbours, so every point lies on <= s lines of S_B.
# Distances stay within 3 for ANY choice of S_A and S_B, so the two sets can be
# chosen independently (the parent forced S_A = S_B).
#
# ----------------------------------------------------------------------------
# NEW: blocking-line insertion.
#
# A new vertex z on the line side with neighbourhood = all q+1 points of some
# line L reaches every line (every two lines meet), every B-vertex (its
# neighbour L∩j is adjacent to y_j), every point and every A-vertex within
# distance 3, and every other inserted vertex. Dually, a new point-side vertex
# w with neighbourhood = the q+1 lines through a point P0 is valid as well.
# Such vertices only need spare capacity on the q+1 vertices they touch, so
# they are added greedily in random order over many trials. Every insertion
# is re-checked by lib.is_valid at the end.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _fits(S, incid, cap, m):
    """True if every resource r is used by at most cap members of S (incid[x] = resources of x)."""
    cnt = [0] * m
    for x in S:
        for r in incid[x]:
            cnt[r] += 1
            if cnt[r] > cap:
                return False
    return True


def _greedy_cap(m, incid, cap, rng, trials, deadline):
    """Randomized maximal set S of items with every resource used <= cap times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for x in order:
            res = incid[x]
            if all(cnt[r] < cap for r in res):
                S.append(x)
                for r in res:
                    cnt[r] += 1
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


def _best_side(q, s, incid, index, F, m, rng, deadline):
    """Largest of a randomized greedy set and the conic set that respects the cap s."""
    S = _greedy_cap(m, incid, s, rng, 30, deadline)
    if s >= 2 and F is not None:
        cs = _conic_set(q, index, F)
        if _fits(cs, incid, s, m) and len(cs) > len(S):
            S = cs
    return S


def _build_arc_graph(m, edges, pl, lp, SA, SB):
    """PG incidence plus A-vertices (over SA, points) and B-vertices (over SB, lines)."""
    kA, kB = len(SA), len(SB)
    n = 2 * m + kA + kB
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + kA + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _blocking_insert(n, edges, d, m, pl, lp, rng, deadline, trials=30):
    """Greedy insertion of line-blocking vertices (new z = points of a line, new w = lines through a point)."""
    base_deg = [0] * n
    for u, v in edges:
        base_deg[u] += 1
        base_deg[v] += 1
    cands = [("z", L) for L in range(m)] + [("w", P) for P in range(m)]
    cands = cands + cands  # allow a second use of the same spare-rich neighbourhood
    best_n, best_E = n, list(edges)
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        deg = base_deg[:]
        E = list(edges)
        nn = n
        order = cands[:]
        rng.shuffle(order)
        for kind, idx in order:
            if kind == "z":
                nbr = lp[idx]                      # points on line idx
            else:
                nbr = [m + L for L in pl[idx]]     # lines through point idx
            if len(nbr) > d or any(deg[v] >= d for v in nbr):
                continue
            for v in nbr:
                deg[v] += 1
                E.append((v, nn))
            deg.append(len(nbr))
            nn += 1
        if nn > best_n:
            best_n, best_E = nn, E
    return best_n, best_E


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates (parent's _augment).
# ----------------------------------------------------------------------------

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


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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

    arc_top = None
    if D >= 3:
        arc_end = start + 0.22 * time_limit
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            if time.monotonic() > arc_end:
                break
            s = d - q - 1
            m, edges, pl, lp, index, pts = _pg_data(q)
            F = lib.GF(q) if s >= 2 else None
            SA = _best_side(q, s, pl, index, F, m, rng, arc_end)
            SB = _best_side(q, s, lp, index, F, m, rng, arc_end)
            n_g, E_g = _build_arc_graph(m, edges, pl, lp, SA, SB)
            n_b, E_b = _blocking_insert(n_g, E_g, d, m, pl, lp, rng, arc_end)
            consider(n_g, E_g)
            consider(n_b, E_b)
            if arc_top is None or n_b > arc_top[0]:
                arc_top = (n_b, E_b)

        if arc_top is not None and time.monotonic() < start + 0.45 * time_limit:
            n_a, e_a = _augment(arc_top[0], arc_top[1], d, D, rng, start + 0.45 * time_limit)
            consider(n_a, e_a)

    if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts.
    search_end = start + 0.62 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < search_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
        if res is not None:
            consider(res[0], res[1])

    # Final greedy insertion on the best graph found so far.
    if D >= 2 and time.monotonic() < start + 0.90 * time_limit:
        n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.90 * time_limit)
        consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
