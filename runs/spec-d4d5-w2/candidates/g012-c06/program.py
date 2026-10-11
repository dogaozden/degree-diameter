import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base geometries.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


# ----------------------------------------------------------------------------
# NEW: doubling search. Two copies of a d-regular bipartite base graph; in each
# copy remove one perfect matching (degree d-1), then join the copies by two
# per-side bijections (degree d again). Simulated annealing over the two
# bijections minimises the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _random_perfect_matching(P, adj_pts, rng):
    """Random perfect matching of a bipartite graph (points 0..P-1, lines 0..P-1); point -> line or None."""
    nbrs = [rng.sample(a, len(a)) for a in adj_pts]
    match_line = [-1] * P

    def aug(u, seen):
        for j in nbrs[u]:
            if not seen[j]:
                seen[j] = True
                if match_line[j] == -1 or aug(match_line[j], seen):
                    match_line[j] = u
                    return True
        return False

    for u in rng.sample(range(P), P):
        if not aug(u, [False] * P):
            return None
    match_pt = [-1] * P
    for j, u in enumerate(match_line):
        match_pt[u] = j
    return match_pt


def _doubled_adj(P, inner, pi1, pi2):
    """Adjacency of the doubled graph with 4P vertices.

    Copy c, base vertex v -> c*2P + v. Base vertices 0..P-1 are points, P..2P-1 lines.
    Copy 0 keeps its colouring; copy 1 has the colouring flipped. Cross edges:
    copy0 point a -- copy1 point pi1[a]; copy0 line P+j -- copy1 line P+pi2[j].
    """
    N = 4 * P
    adj = [[] for _ in range(N)]
    for c in (0, 1):
        off = c * 2 * P
        for v in range(2 * P):
            adj[off + v] = [off + w for w in inner[v]]
    for a in range(P):
        x, y = a, 2 * P + pi1[a]
        adj[x].append(y)
        adj[y].append(x)
    for j in range(P):
        x, y = P + j, 3 * P + pi2[j]
        adj[x].append(y)
        adj[y].append(x)
    return adj


def _bad_pairs_adj(adj, N, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _anneal_double(P, inner, D, deadline, rng):
    """Anneal the two cross bijections; return (n, edges) with zero bad pairs, or None."""
    N = 4 * P
    pi1 = list(range(P))
    rng.shuffle(pi1)
    pi2 = list(range(P))
    rng.shuffle(pi2)
    cost = _bad_pairs_adj(_doubled_adj(P, inner, pi1, pi2), N, D)
    best_cost = cost
    best_state = (pi1[:], pi2[:])
    stall = 0
    it = 0
    while cost > 0 and time.monotonic() < deadline:
        it += 1
        T = max(0.3, 1.5 * (0.9995 ** it))
        perm = pi1 if rng.random() < 0.5 else pi2
        i = rng.randrange(P)
        j = rng.randrange(P)
        if i == j:
            continue
        perm[i], perm[j] = perm[j], perm[i]
        c2 = _bad_pairs_adj(_doubled_adj(P, inner, pi1, pi2), N, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_state = (pi1[:], pi2[:])
                stall = 0
            else:
                stall += 1
        else:
            perm[i], perm[j] = perm[j], perm[i]
            stall += 1
        if stall > 6000:
            break
    if best_cost != 0:
        return None
    p1, p2 = best_state
    adj = _doubled_adj(P, inner, p1, p2)
    edges = sorted({(min(u, v), max(u, v)) for u in range(N) for v in adj[u]})
    return N, edges


def _double_search(base_n, base_edges, D, deadline, rng, consider):
    """Repeatedly pick a random perfect matching to delete, then anneal the cross bijections."""
    P = base_n // 2
    adj_pts = [[] for _ in range(P)]
    for u, v in base_edges:
        adj_pts[u].append(v - P)
    while time.monotonic() < deadline:
        mp = _random_perfect_matching(P, adj_pts, rng)
        if mp is None:
            return
        inner = [[] for _ in range(2 * P)]
        for u in range(P):
            for j in adj_pts[u]:
                if j == mp[u]:
                    continue
                inner[u].append(P + j)
                inner[P + j].append(u)
        chunk_deadline = min(deadline, time.monotonic() + 8.0)
        res = _anneal_double(P, inner, D, chunk_deadline, rng)
        if res is not None:
            consider(res[0], res[1])
            return


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
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

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
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
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))

    def dl(frac):
        return start + frac * budget

    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    def done():
        return best[0] >= moore

    # Base geometries.
    if D >= 3 and not done():
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, dl(0.12), rng)
            consider(n2, e2)

    if D >= 4 and not done() and d - 1 <= 5 and lib.is_prime_power(d - 1):
        gq_n, gq_e = _gq_w(d - 1)
        consider(gq_n, gq_e)
        # NEW family: doubled generalized quadrangle with annealed cross bijections.
        if D >= 5 and not done():
            _double_search(gq_n, gq_e, D, dl(0.55), rng, consider)

    # Voltage-lift annealing with cover growth.
    if not done():
        ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        anneal_iters = 1500 if D >= 5 else 400
        loop_dl = dl(0.9)
        while time.monotonic() < loop_dl and not done():
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            window = 3 if D >= 5 else max(3, base // 8 + 1)
            G = max(2, base + 1 + rng.randrange(0, window))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, loop_dl, anneal_iters)
            if res is not None:
                consider(res[0], res[1])
                gn, ge = _grow(res[0], res[1], d, D, loop_dl, rng)
                consider(gn, ge)

    # Final growth pass on the best graph found.
    if not done():
        gn, ge = _grow(best[0], best[1], d, D, dl(0.97), rng)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        return fb_n, fb_e
    return best[0], best[1]
