import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers: projective plane, generalized quadrangle and Araujo-Pardo-Lopez bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
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
# Twin cloning (diameter- and bipartiteness-preserving blow-up).
# ----------------------------------------------------------------------------

def _twin_fill(n, edges, d):
    """Repeatedly clone vertices while their neighbours have spare degree. Returns (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed:
        changed = False
        for u in range(len(adj)):
            nb = adj[u]
            if not nb or len(nb) > d:
                continue
            cap = min(d - deg[w] for w in nb)
            for _ in range(cap):
                v = len(adj)
                adj.append(list(nb))
                deg.append(len(nb))
                for w in nb:
                    adj[w].append(v)
                    deg[w] += 1
                changed = True
    out = []
    for v in range(len(adj)):
        for w in adj[v]:
            if w > v:
                out.append((v, w))
    return len(adj), out


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
# Insertion with edge displacement and 2-switch repair.
# ----------------------------------------------------------------------------

def _insert_repair(n, edges, d, D, deadline, rng, attempts=12, steps=150):
    """Try to insert one vertex and repair to diameter D. Returns (n+1, edges) or None."""
    base = {(min(u, v), max(u, v)) for u, v in edges}
    adj0 = [[] for _ in range(n)]
    for u, v in base:
        adj0[u].append(v)
        adj0[v].append(u)
    color = _bipartition(n, adj0)
    cand_side = [v for v in range(n) if color[v] == 1]
    if not cand_side:
        return None

    for _ in range(attempts):
        if time.monotonic() >= deadline:
            break
        es = set(base)
        nb = [set(a) for a in adj0]
        deg = [len(a) for a in adj0]
        v = n
        nb.append(set())
        deg.append(0)
        colr = color + [0]

        B = rng.sample(cand_side, min(d, len(cand_side)))
        for b in B:
            if deg[b] >= d:
                x = rng.choice(sorted(nb[b]))
                nb[b].discard(x)
                nb[x].discard(b)
                es.discard((min(x, b), max(x, b)))
                deg[b] -= 1
                deg[x] -= 1
            es.add((b, v))
            nb[b].add(v)
            nb[v].add(b)
            deg[b] += 1
            deg[v] += 1

        left = [u for u in range(n + 1) if colr[u] == 0 and deg[u] < d]
        right = [u for u in range(n + 1) if colr[u] == 1 and deg[u] < d]
        for _ in range(4 * (len(left) + len(right)) + 4):
            if not left or not right:
                break
            a = rng.choice(left)
            b = rng.choice(right)
            key = (min(a, b), max(a, b))
            if key in es:
                continue
            es.add(key)
            nb[a].add(b)
            nb[b].add(a)
            deg[a] += 1
            deg[b] += 1
            if deg[a] >= d:
                left.remove(a)
            if deg[b] >= d:
                right.remove(b)

        cur = lib.bad_pairs(n + 1, list(es), D)
        for _ in range(steps):
            if cur == 0 or time.monotonic() >= deadline:
                break
            e1, e2 = rng.sample(list(es), 2)
            a0 = e1[0] if colr[e1[0]] == 0 else e1[1]
            b1 = e1[1] if a0 == e1[0] else e1[0]
            c0 = e2[0] if colr[e2[0]] == 0 else e2[1]
            b2 = e2[1] if c0 == e2[0] else e2[0]
            if a0 == c0 or b1 == b2:
                continue
            k1 = (min(a0, b2), max(a0, b2))
            k2 = (min(c0, b1), max(c0, b1))
            if k1 in es or k2 in es:
                continue
            es.discard(e1)
            es.discard(e2)
            es.add(k1)
            es.add(k2)
            new = lib.bad_pairs(n + 1, list(es), D)
            if new <= cur:
                cur = new
            else:
                es.discard(k1)
                es.discard(k2)
                es.add(e1)
                es.add(e2)
        if cur == 0:
            return n + 1, sorted(es)
    return None


def _grow_repair(n, edges, d, D, deadline, rng):
    """Repeatedly insert repaired vertices until the deadline or a failed insertion."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        res = _insert_repair(cur_n, cur_e, d, D, deadline, rng)
        if res is None:
            break
        cur_n, cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: greedy best-improvement Haar construction.
#
# Instead of random hill-climbing on the connection set S of a Haar graph
# H(m, S), we grow S one shift at a time, always adding the shift that leaves
# the fewest pairs at distance > D (a full scan of Z_m at each step). Then we
# run best-improvement swaps until the count reaches zero or time runs out.
# Haar graphs are bipartite and d-regular, so validity only needs the diameter.
# ----------------------------------------------------------------------------

def _greedy_haar(d, D, m, deadline):
    """Greedy construction of S (|S| = d, 0 in S) in Z_m with diameter <= D for H(m, S). Or None."""
    if m - 1 < d - 1:
        return None

    def bad(S):
        n, e = lib.haar_graph(m, S)
        return lib.bad_pairs(n, e, D)

    S = [0]
    cur = None
    while len(S) < d:
        if time.monotonic() >= deadline:
            return None
        best_c, best_v = None, None
        for c in range(1, m):
            if c in S:
                continue
            v = bad(S + [c])
            if best_v is None or v < best_v:
                best_v, best_c = v, c
            if time.monotonic() >= deadline:
                return None
        if best_c is None:
            return None
        S.append(best_c)
        cur = best_v
    if cur is None:
        cur = bad(S)

    improved = True
    while cur > 0 and improved:
        if time.monotonic() >= deadline:
            break
        improved = False
        for i in range(1, d):
            for c in range(1, m):
                if c in S:
                    continue
                T = S[:]
                T[i] = c
                v = bad(T)
                if v < cur:
                    S, cur, improved = T, v, True
                    break
                if time.monotonic() >= deadline:
                    break
            if improved or time.monotonic() >= deadline:
                break
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups_of_order(G, rng, cap=8):
    """All semidirect products Z_m x| Z_k2 of order G (sampled down to `cap` multipliers each)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if len(rs) > cap:
                rs = rng.sample(rs, cap)
        for r in rs:
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            out.append((order, mul))
    return out


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
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

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
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
        if D >= 2 and n > 0:
            n, e = _twin_fill(n, e, d)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.30 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng)
            consider(n2, e2)

    # NEW: greedy Haar construction at increasing orders, for diameter 3 and 4.
    if D in (3, 4):
        greedy_deadline = start + 0.45 * time_limit
        m = max(d + 1, best_n // 2 + 1)
        misses = 0
        while time.monotonic() < greedy_deadline and misses < 3:
            S = _greedy_haar(d, D, m, greedy_deadline)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                m += max(1, m // 50)
                misses = 0
            else:
                misses += 1
                m += 1

    if D >= 5:
        rng2 = random.Random(seed * 104729 + d * 31 + D)
        while time.monotonic() < deadline:
            k = rng2.choice([1, 1, 2])
            base = best_n // (2 * k)
            span = max(4, base // 4)
            G = base + 1 + rng2.randrange(span)
            groups = _groups_of_order(G, rng2)
            if not groups:
                continue
            order, mul = rng2.choice(groups)
            remaining = deadline - time.monotonic()
            slice_end = time.monotonic() + max(1.5, remaining / 6.0)
            attempt_deadline = min(deadline, slice_end)
            res = _anneal(d, D, k, order, mul, rng2, attempt_deadline, iters=2500)
            if res is not None:
                consider(res[0], res[1])
    else:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        haar_m, haar_miss = d + 1, 0
        while time.monotonic() < deadline:
            if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
                S = _search_haar(d, D, haar_m, rng, deadline, 120)
                if S is not None:
                    n, e = lib.haar_graph(haar_m, S)
                    consider(n, e)
                    haar_miss = 0
                else:
                    haar_miss += 1
                haar_m += 1
                continue

            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = None
            groups = _groups_of_order(G, rng)
            if groups:
                g = rng.choice(groups)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    # Final phase: grow the best graph with edge-displacement insertion and 2-switch repair.
    if D >= 3 and best_n > 1:
        rng3 = random.Random(seed * 2654435761 + d * 13 + D)
        n3, e3 = _grow_repair(best[0], best[1], d, D, start + 0.85 * time_limit, rng3)
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
