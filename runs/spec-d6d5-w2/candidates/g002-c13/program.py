import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Deterministic bases (projective plane, Araujo-Pardo-Lopez, arc extensions).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# Cover / saturation growth (used on the projective-plane base).
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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# New construction for D >= 5: bi-Cayley graphs over semidirect products.
#
# Vertices A_g = g and B_h = G + h, with G = |group|, identity coded 0.
# Edges A_g ~ B_{g*s} for s in S, where |S| = d and S is a set of distinct
# group elements. Left multiplication is an automorphism, so distances from
# A_e and B_e suffice to check the whole graph:
#   cost = (G - #A reached from A_e) + (G - #B reached from A_e)
#          + (G - #B reached from B_e).
# Zero cost means diameter <= D.
# ----------------------------------------------------------------------------

def _group_options(G, max_k=12):
    """All (m, k, r) with m * k = G giving a valid semidirect product Z_m x| Z_k."""
    opts = []
    for k in range(1, min(max_k, G) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _bfs_counts(G, T, S, Sinv, D, side):
    """Return [#A reached, #B reached] by BFS of depth D from identity on the given side."""
    seen = [bytearray(G), bytearray(G)]
    seen[side][0] = 1
    cnt = [0, 0]
    cnt[side] = 1
    front = [0]
    s_side = side
    for _ in range(D):
        nxt = []
        if s_side == 0:
            for g in front:
                row = T[g]
                for s in S:
                    h = row[s]
                    if not seen[1][h]:
                        seen[1][h] = 1
                        nxt.append(h)
        else:
            for x in front:
                row = T[x]
                for t in Sinv:
                    g = row[t]
                    if not seen[0][g]:
                        seen[0][g] = 1
                        nxt.append(g)
        cnt[1 - s_side] += len(nxt)
        front = nxt
        s_side ^= 1
        if not front:
            break
    return cnt


def _bicayley_cost(G, T, S, D):
    Sinv = [_INV[s] for s in S] if False else None  # placeholder, replaced below
    raise RuntimeError  # never called; see _cost_with_inv


def _cost_with_inv(G, T, Inv, S, D):
    Sinv = [Inv[s] for s in S]
    cA = _bfs_counts(G, T, S, Sinv, D, 0)
    cB = _bfs_counts(G, T, S, Sinv, D, 1)
    return (G - cA[0]) + (G - cA[1]) + (G - cB[1])


def _search_group(G, T, Inv, d, D, rng, deadline):
    """Simulated annealing over the connection set S of size d. Returns S or None."""
    S = rng.sample(range(G), d)
    c = _cost_with_inv(G, T, Inv, S, D)
    it = 0
    while c > 0 and time.monotonic() < deadline:
        it += 1
        temp = max(0.15, 2.0 * (0.995 ** it))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost_with_inv(G, T, Inv, S2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
    return S if c == 0 else None


def _bicayley_edges(G, T, S):
    E = []
    for g in range(G):
        row = T[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        for n_c, e_c in _arc_extensions(d, start + 0.12 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 5:
        # Bi-Cayley search: aim just above the current best order.
        fails = 0
        group_cache = {}
        table_cache = {}
        while time.monotonic() < deadline:
            G = best_n // 2 + 1 + min(fails // 4, 6)
            opts = group_cache.get(G)
            if opts is None:
                opts = _group_options(G)
                group_cache[G] = opts
            if not opts:
                fails += 1
                continue
            m, k, r = rng.choice(opts)
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, s) for s in range(order)] for x in range(order)]
            Inv = [inv(s) for s in range(order)]
            budget = min(deadline, time.monotonic() + 6.0)
            S = _search_group(order, T, Inv, d, D, rng, budget)
            if S is not None:
                n, e = _bicayley_edges(order, T, S)
                before = best_n
                consider(n, e)
                if best_n > before:
                    fails = 0
                else:
                    fails += 1
            else:
                fails += 1
        table_cache.clear()

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
