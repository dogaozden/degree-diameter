import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc-extended plane graphs (diameter 3).
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
# Cover-based vertex extension and saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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
# Bi-Cayley voltage lifts over Z_m x| Z_k (annealed), for D >= 5.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
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
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW MAIN SEARCH: unstructured bipartite local search with growth.
#
# The graph is kept as explicit bipartite adjacency sets (A side, B side).
# Moves are degree-safe: 2-switches, endpoint rewires onto spare-degree
# vertices, and additions between spare-degree vertices. The cost is the
# number of unordered vertex pairs at distance > D (computed with bitmask
# BFS). When the cost reaches zero, the graph is valid; it is recorded and
# grown by one A vertex and one B vertex, then annealed again. If a level
# stalls, the search restarts that level from the last valid graph.
# ----------------------------------------------------------------------------

def _to_state(n, edges):
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    idxA, idxB = {}, {}
    for v in range(n):
        if color[v] == 0:
            idxA[v] = len(idxA)
        else:
            idxB[v] = len(idxB)
    nA, nB = len(idxA), len(idxB)
    adjA = [set() for _ in range(nA)]
    adjB = [set() for _ in range(nB)]
    for u, v in edges:
        if color[u] == 1:
            u, v = v, u
        a = idxA[u]
        b = idxB[v]
        adjA[a].add(b)
        adjB[b].add(a)
    return nA, nB, adjA, adjB


def _to_global(nA, adjA):
    return [(i, nA + j) for i in range(len(adjA)) for j in adjA[i]]


def _bad_count(nA, nB, adjA, adjB, D):
    n = nA + nB
    adj = [None] * n
    for i in range(nA):
        adj[i] = [nA + j for j in adjA[i]]
    for j in range(nB):
        adj[nA + j] = adjB[j]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _saturate_state(nA, nB, adjA, adjB, d, rng):
    spA = [i for i in range(nA) if len(adjA[i]) < d]
    spB = [j for j in range(nB) if len(adjB[j]) < d]
    pairs = [(i, j) for i in spA for j in spB if j not in adjA[i]]
    rng.shuffle(pairs)
    for i, j in pairs:
        if len(adjA[i]) < d and len(adjB[j]) < d and j not in adjA[i]:
            adjA[i].add(j)
            adjB[j].add(i)


def _apply(ops, adjA, adjB):
    for kind, i, j in ops:
        if kind:
            adjA[i].add(j)
            adjB[j].add(i)
        else:
            adjA[i].discard(j)
            adjB[j].discard(i)


def _undo(ops, adjA, adjB):
    for kind, i, j in reversed(ops):
        if kind:
            adjA[i].discard(j)
            adjB[j].discard(i)
        else:
            adjA[i].add(j)
            adjB[j].add(i)


def _propose(nA, nB, adjA, adjB, d, rng):
    r = rng.random()
    if r < 0.5:
        i1 = rng.randrange(nA)
        if not adjA[i1]:
            return None
        j1 = rng.choice(list(adjA[i1]))
        i2 = rng.randrange(nA)
        if i2 == i1 or not adjA[i2]:
            return None
        j2 = rng.choice(list(adjA[i2]))
        if j2 in adjA[i1] or j1 in adjA[i2]:
            return None
        return [(0, i1, j1), (0, i2, j2), (1, i1, j2), (1, i2, j1)]
    elif r < 0.75:
        i = rng.randrange(nA)
        if not adjA[i]:
            return None
        j1 = rng.choice(list(adjA[i]))
        j2 = rng.randrange(nB)
        if j2 == j1 or j2 in adjA[i] or len(adjB[j2]) >= d:
            return None
        return [(0, i, j1), (1, i, j2)]
    elif r < 0.9:
        j = rng.randrange(nB)
        if not adjB[j]:
            return None
        i1 = rng.choice(list(adjB[j]))
        i2 = rng.randrange(nA)
        if i2 == i1 or i2 in adjB[j] or len(adjA[i2]) >= d:
            return None
        return [(0, i1, j), (1, i2, j)]
    else:
        i = rng.randrange(nA)
        j = rng.randrange(nB)
        if len(adjA[i]) >= d or len(adjB[j]) >= d or j in adjA[i]:
            return None
        return [(1, i, j)]


def _anneal_state(nA, nB, adjA, adjB, d, D, rng, deadline, max_iters):
    cost = _bad_count(nA, nB, adjA, adjB, D)
    it = 0
    cycle = 4000
    while cost > 0 and it < max_iters:
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        it += 1
        phase = it % cycle
        T = 0.5 + 2.5 * (1.0 - phase / cycle) ** 2
        ops = _propose(nA, nB, adjA, adjB, d, rng)
        if ops is None:
            continue
        _apply(ops, adjA, adjB)
        c2 = _bad_count(nA, nB, adjA, adjB, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _undo(ops, adjA, adjB)
    return cost


def _grow_search(n0, edges, d, D, deadline, rng, consider):
    nA, nB, adjA, adjB = _to_state(n0, edges)
    base = (nA, nB, [set(s) for s in adjA], [set(s) for s in adjB])
    level_budget = 5000
    while time.monotonic() < deadline:
        nA, nB = base[0], base[1]
        adjA = [set(s) for s in base[2]]
        adjB = [set(s) for s in base[3]]
        nA += 1
        nB += 1
        adjA.append(set())
        adjB.append(set())
        _saturate_state(nA, nB, adjA, adjB, d, rng)
        cost = _anneal_state(nA, nB, adjA, adjB, d, D, rng, deadline, level_budget)
        if cost == 0:
            base = (nA, nB, [set(s) for s in adjA], [set(s) for s in adjB])
            consider(nA + nB, _to_global(nA, adjA))


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.85 * time_limit

    def at(frac):
        return start + frac * budget

    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)

    if D >= 3 and best_n < moore:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, at(0.10), rng)
                consider(n2, e2)
            for n_c, e_c in _arc_extensions(d, at(0.15), random.Random(seed * 7919 + d)):
                consider(n_c, e_c)
        except Exception:
            pass

    # Structured voltage-lift stage (D >= 5), kept as a seed source.
    if D >= 5 and best_n < moore:
        try:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
            while time.monotonic() < at(0.40):
                k = rng.choice(ks)
                base = best_n // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, at(0.40), anneal_iters)
                if res is not None:
                    consider(res[0], res[1])
                    gn, ge = _grow(res[0], res[1], d, D, at(0.40), rng)
                    consider(gn, ge)
        except Exception:
            pass

    # Bold stage: unstructured annealed local search with growth, seeded from best.
    if D >= 3 and best_n < moore:
        try:
            _grow_search(best[0], best[1], d, D, at(0.98), rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
