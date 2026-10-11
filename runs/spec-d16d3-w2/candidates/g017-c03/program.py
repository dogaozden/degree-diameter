import random
import time

import lib


# ---------------------------------------------------------------- adjacency utilities

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if u != v:
            adj[u].add(v)
            adj[v].add(u)
    return adj


def _adj_to_edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _colors(n, adj):
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


def _balls(n, adj, r):
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


def _diam_ok(n, adj, D):
    full = (1 << n) - 1
    return all(b == full for b in _balls(n, adj, D))


# ---------------------------------------------------------------- projective plane and arcs

def _best_pg(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_index(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
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


def _arc_extensions(d, deadline, rng, threshold):
    """Arc-extended PG(2,q) graphs for prime powers q with spare degree s = d - q - 1 >= 1."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index = _pg_index(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len)
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ---------------------------------------------------------------- new helper: rewiring insertion

def _rewire_insert(n, adj, d, D, deadline, rng, max_rm, cap):
    """Insert new vertices whose neighbourhoods cover everything within D-1, allowing up to
    max_rm saturated neighbours to give up one edge each. Each insertion is accepted only if
    the whole graph still has diameter <= D, so the result is always valid.
    Adding a vertex on side 1-c adjacent only to side c keeps bipartiteness."""
    if D < 2:
        return n
    color = _colors(n, adj)
    while time.monotonic() < deadline and n < cap:
        full = (1 << n) - 1
        ball = _balls(n, adj, D - 1)
        c = rng.randrange(2)
        pool = [s for s in range(n) if color[s] == c]
        rng.shuffle(pool)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and pool:
            best_i, best_sc = -1, None
            for i, s in enumerate(pool):
                g = (ball[s] & ~covered).bit_count()
                if g == 0:
                    continue
                sc = g - (2 if len(adj[s]) >= d else 0)
                if best_sc is None or sc > best_sc:
                    best_sc, best_i = sc, i
            if best_i < 0:
                break
            s = pool.pop(best_i)
            chosen.append(s)
            covered |= ball[s]
        if covered != full:
            continue
        full_ct = sum(1 for s in chosen if len(adj[s]) >= d)
        if full_ct > max_rm:
            continue
        removed = []
        for s in chosen:
            if len(adj[s]) >= d:
                w = rng.choice(sorted(adj[s]))
                adj[s].discard(w)
                adj[w].discard(s)
                removed.append((s, w))
        v = n
        adj.append(set(chosen))
        for s in chosen:
            adj[s].add(v)
        color.append(1 - c)
        n += 1
        if _diam_ok(n, adj, D):
            continue
        # Revert.
        n -= 1
        for s in chosen:
            adj[s].discard(v)
        adj.pop()
        color.pop()
        for s, w in removed:
            adj[s].add(w)
            adj[w].add(s)
    return n


# ---------------------------------------------------------------- cover extension, saturation, twins

def _cover_pick(cands, ball, full, d, rng):
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_i, best_g = -1, 0
        for i, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g:
                best_g, best_i = g, i
        if best_i < 0:
            break
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, adj, d, D, deadline, rng):
    """Add vertices with spare-degree neighbours covering everything within D-1."""
    if D < 2:
        return n
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        color = _colors(n, adj)
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = None
            for _ in range(20):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover_pick(cands, ball, full, d, rng)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                adj.append(set(chosen))
                for s in chosen:
                    adj[s].add(v)
                added = True
                break
        if not added:
            break
    return n


def _saturate(n, adj, d, rng):
    """Join deficient opposite-side vertices. Adding edges never increases distances."""
    color = _colors(n, adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


def _twin_saturate(n, adj, d, D, rng, deadline):
    """Add twins (same neighbourhood) of vertices whose neighbours all have spare degree.
    Twins preserve all distances between old vertices and keep the diameter <= D for D >= 2."""
    if D < 2:
        return n
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        adj.append(set(adj[v]))
        for u in list(adj[t]):
            adj[u].add(t)
    return n


def _refine(n, adj, d, D, deadline, rng, cap):
    """Alternate cover extension, rewiring insertion, saturation and twins until time runs out."""
    while time.monotonic() < deadline and n < cap:
        before_n = n
        before_deg = sum(len(a) for a in adj)
        left = deadline - time.monotonic()
        n = _extend_cover(n, adj, d, D, time.monotonic() + 0.2 * left, rng)
        left = deadline - time.monotonic()
        n = _rewire_insert(n, adj, d, D, time.monotonic() + 0.6 * left, rng, 3, cap)
        _saturate(n, adj, d, rng)
        left = deadline - time.monotonic()
        n = _twin_saturate(n, adj, d, D, rng, time.monotonic() + 0.5 * left)
        if n == before_n and sum(len(a) for a in adj) == before_deg:
            break
    return n


# ---------------------------------------------------------------- main

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.8 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    cap = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    q = _best_pg(d)
    if q is None:
        return best_n, best_e

    n0, e0 = lib.projective_plane_incidence(q)
    consider(n0, e0)
    if best_n >= cap:
        return best_n, best_e

    arcs = _arc_extensions(d, start + 0.45 * T, random.Random(seed * 7919 + d), best_n)
    for n_c, e_c in arcs:
        consider(n_c, e_c)

    pool = [(n0, e0)] + arcs
    pool.sort(key=lambda x: -x[0])
    pool = pool[:2]
    for idx, (n_c, e_c) in enumerate(pool):
        now = time.monotonic()
        if now >= deadline or best_n >= cap:
            break
        share = (deadline - now) / (len(pool) - idx)
        adj = _to_adj(n_c, e_c)
        n_r = _refine(n_c, adj, d, D, now + share, rng, cap)
        consider(n_r, _adj_to_edges(adj))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
