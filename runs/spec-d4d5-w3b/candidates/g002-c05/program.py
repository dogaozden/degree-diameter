import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane bases and arc-extended graphs (diameter 3).
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search that grows a feasible load-bounded set S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
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
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Remove-and-regrow plateau walk.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, v):
    """Delete vertex v and compact the labels to 0..n-2."""
    mp = {}
    j = 0
    for x in range(n):
        if x != v:
            mp[x] = j
            j += 1
    E = [(mp[a], mp[b]) for a, b in edges if a != v and b != v]
    return n - 1, E


def _remove_regrow_walk(n, edges, d, D, deadline, rng):
    """Plateau walk by remove-and-regrow; returns the best valid (n, edges) seen."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        v = rng.randrange(cur_n)
        n1, e1 = _remove_vertex(cur_n, cur_e, v)
        n2, e2 = _grow(n1, e1, d, D, deadline, rng)
        if n2 >= cur_n and lib.is_valid(n2, e2, d, D):
            cur_n, cur_e = n2, e2
            if cur_n > best_n:
                best_n, best_e = cur_n, list(cur_e)
    return best_n, best_e


# ----------------------------------------------------------------------------
# Edge-split insertion with bipartite double-edge-swap repair.
# ----------------------------------------------------------------------------

def _split_insert_repair(n, edges, d, D, rng, deadline, iters):
    """Insert two vertices by edge splitting, then repair by swaps; (n+2, edges) if valid, else None."""
    edges = list(edges)
    if len(edges) < d or n < 2:
        return None
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)

    order = list(range(len(edges)))
    rng.shuffle(order)
    used_x, used_y, chosen = set(), set(), []
    for i in order:
        a, b = edges[i]
        if color[a] == 1:
            a, b = b, a
        if a in used_x or b in used_y:
            continue
        used_x.add(a)
        used_y.add(b)
        chosen.append((a, b))
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None

    gone = {(min(a, b), max(a, b)) for a, b in chosen}
    E = [e for e in edges if (min(e[0], e[1]), max(e[0], e[1])) not in gone]
    v, w = n, n + 1
    E.extend((v, b) for _, b in chosen)
    E.extend((a, w) for a, _ in chosen)
    n2 = n + 2
    col = color + [0, 1]
    S = {(min(a, b), max(a, b)) for a, b in E}

    cur = lib.bad_pairs(n2, E, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        old1, old2 = E[i], E[j]
        a, b = old1
        c, e = old2
        if col[a] == 1:
            a, b = b, a
        if col[c] == 1:
            c, e = e, c
        if a == c or b == e:
            continue
        k1 = (min(a, e), max(a, e))
        k2 = (min(c, b), max(c, b))
        if k1 in S or k2 in S or k1 == k2:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = lib.bad_pairs(n2, E, D)
        if new <= cur:
            S.discard((min(old1[0], old1[1]), max(old1[0], old1[1])))
            S.discard((min(old2[0], old2[1]), max(old2[0], old2[1])))
            S.add(k1)
            S.add(k2)
            cur = new
        else:
            E[i] = old1
            E[j] = old2

    if cur == 0:
        return n2, E
    return None


# ----------------------------------------------------------------------------
# NEW: mixed-action bi-Cayley voltage lifts.
#
# A dart carries a permutation pi of the group G, and the lift joins
# (layer i, g) to (layer k+j, pi(g)). Pure voltage lifts only use right
# translations g -> g*s. Here each dart draws its permutation from four
# families, all bijections of G:
#   0: g -> g*s              (right translation)
#   1: g -> s*g              (left translation)
#   2: g -> (g^-1 * s) * t   (inversion, then translations)
#   3: g -> (s*g) * t        (two-sided translation)
# Each layer still matches the k A-vertices to k B-vertices by a permutation,
# so every degree stays exactly d. Because the families mix, the search reaches
# lifts that no single right-translation voltage assignment produces.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul, inv) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
            order, mul, inv = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _mk_perm(G, mul, inv, typ, s, t):
    """Permutation of range(G) for a mixed-action dart (see the section comment)."""
    if typ == 0:
        return [mul(g, s) for g in range(G)]
    if typ == 1:
        return [mul(s, g) for g in range(G)]
    if typ == 2:
        return [mul(mul(inv(g), s), t) for g in range(G)]
    return [mul(mul(s, g), t) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(x[0], x[1], tuple(pm)) for x, pm in zip(darts, perms)}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for x, pm in zip(darts, perms):
        i, j = x[0], x[1]
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
    for x, pm in zip(darts, perms):
        i, j = x[0], x[1]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, inv, rng, deadline, iters):
    """Simulated annealing over mixed-action darts and per-layer target assignments."""
    darts = []  # dart = [i, j, typ, s, t]
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(4), rng.randrange(G), rng.randrange(G)])
    perms = [_mk_perm(G, mul, inv, x[2], x[3], x[4]) for x in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_dart = darts[idx][:]
            old_perm = perms[idx]
            darts[idx][2] = rng.randrange(4)
            darts[idx][3] = rng.randrange(G)
            darts[idx][4] = rng.randrange(G)
            perms[idx] = _mk_perm(G, mul, inv, darts[idx][2], darts[idx][3], darts[idx][4])
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx] = old_dart
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
    main_deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Main search: annealed mixed-action lifts over semidirect products.
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
    else:
        ks = [1, 1, 2, 3]
        anneal_iters = 400
    while time.monotonic() < main_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul, inv = g
        res = _anneal(d, D, k, order, mul, inv, rng, main_deadline, anneal_iters)
        if res is not None:
            consider(res[0], res[1])
            if D >= 5:
                gn, ge = _grow(res[0], res[1], d, D, main_deadline, rng)
                consider(gn, ge)

    # Edge-split insertion (+2 vertices per success) with swap repair.
    if D >= 5:
        ins_deadline = start + 0.85 * time_limit
        miss = 0
        while time.monotonic() < ins_deadline and miss < 6:
            r = _split_insert_repair(best[0], best[1], d, D, rng, ins_deadline, 300)
            if r is None:
                miss += 1
                continue
            consider(r[0], r[1])
            gn, ge = _grow(r[0], r[1], d, D, ins_deadline, rng)
            consider(gn, ge)

    # Remove-and-regrow plateau walk on the best graph.
    if D >= 5:
        wn, we = _remove_regrow_walk(best[0], best[1], d, D, start + 0.92 * time_limit, rng)
        consider(wn, we)

    # Final growth pass on the best graph found.
    if D >= 5:
        gn, ge = _grow(best[0], best[1], d, D, start + 0.95 * time_limit, rng)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
