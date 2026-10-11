import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact one-vertex extension test (new routine).
#
# Let G be valid with diameter <= D and bipartite. Add a vertex x joined to a
# set N of vertices, all on one side, each with spare degree. Old distances
# can only shrink, and dist(x, w) = 1 + min_{u in N} dist(u, w). So G + x has
# diameter <= D exactly when the radius-(D-1) balls of the vertices in N cover
# every vertex of G. Coloring x opposite to N keeps the graph bipartite.
#
# grow() repeatedly finds such a cover by randomized greedy set cover over
# spare-capacity vertices. Stars of PG(2,q) are the special case where the
# cover is a full line or pencil.
#
# search() is an iterated local search. It removes a random added vertex,
# keeps the removal only if the graph is still valid, regrows greedily, and
# accepts the result when the vertex count does not drop. The best valid
# graph seen is returned.
# ----------------------------------------------------------------------------


def _bip_colors(adj):
    color = {}
    for s in adj:
        if s in color:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(adj, R):
    """Return (ids, pos, masks): masks[pos[v]] is the bitmask of the radius-R ball of v."""
    ids = list(adj)
    pos = {v: i for i, v in enumerate(ids)}
    nb = [[pos[u] for u in adj[v]] for v in ids]
    reach = [1 << i for i in range(len(ids))]
    for _ in range(R):
        new = []
        for i in range(len(ids)):
            r = reach[i]
            for j in nb[i]:
                r |= reach[j]
            new.append(r)
        reach = new
    return ids, pos, reach


def _find_cover(cands, full, d, rng, noise):
    """Greedy cover of the bitmask `full` by at most d candidate masks; returns vertex list or None."""
    covered = 0
    chosen = []
    pool = list(cands)
    while covered != full:
        if len(chosen) >= d:
            return None
        bi = -1
        bs = -1.0
        for i, (msk, _v) in enumerate(pool):
            g = (msk & ~covered).bit_count()
            if g == 0:
                continue
            sc = g + noise * rng.random()
            if sc > bs:
                bs = sc
                bi = i
        if bi < 0:
            return None
        msk, v = pool.pop(bi)
        chosen.append(v)
        covered |= msk
    return chosen


def _grow(adj, color, added, d, D, rng, deadline, tries):
    """Greedily add vertices with exact radius-(D-1) cover tests until none fits."""
    R = D - 1
    while time.monotonic() < deadline:
        ids, pos, masks = _ball_masks(adj, R)
        full = (1 << len(ids)) - 1
        done = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [(masks[pos[v]], v) for v in ids
                     if color[v] == c and len(adj[v]) < d]
            if not cands:
                continue
            for t in range(tries):
                noise = (0.0, 0.3, 1.0, 3.0)[t % 4]
                chosen = _find_cover(cands, full, d, rng, noise)
                if chosen is not None:
                    x = max(adj) + 1
                    adj[x] = set(chosen)
                    for u in chosen:
                        adj[u].add(x)
                    color[x] = 1 - c
                    added.add(x)
                    done = True
                    break
            if done:
                break
        if not done:
            return


def _copy(adj):
    return {v: set(s) for v, s in adj.items()}


def _snapshot(adj):
    return lib.relabel([(u, v) for u in adj for v in adj[u] if u < v])


def _valid_adj(adj, d, D):
    n, E = lib.relabel([(u, v) for u in adj for v in adj[u] if u < v])
    return lib.is_valid(n, E, d, D)


def _search(n0, E0, d, D, deadline, rng):
    adj = {v: set() for v in range(n0)}
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    color = _bip_colors(adj)
    added = set()
    _grow(adj, color, added, d, D, rng, deadline, tries=30)
    best_cnt = len(adj)
    best = _snapshot(adj)
    while time.monotonic() < deadline and added:
        saved = (_copy(adj), dict(color), set(added))
        k = 1 if rng.random() < 0.6 else 2
        for _ in range(k):
            if not added:
                break
            x = rng.choice(sorted(added))
            for u in adj.pop(x):
                adj[u].discard(x)
            added.discard(x)
            color.pop(x, None)
        if not _valid_adj(adj, d, D):
            adj, color, added = saved
            continue
        _grow(adj, color, added, d, D, rng, deadline, tries=12)
        if len(adj) < len(saved[0]):
            adj, color, added = saved
            continue
        if len(adj) > best_cnt:
            best_cnt = len(adj)
            best = _snapshot(adj)
    return best


# ----------------------------------------------------------------------------
# Starting graphs.
# ----------------------------------------------------------------------------

def _prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_data(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
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


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S, point_lines, line_points):
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


def _arc_base(d, rng, deadline):
    """Best arc-extended PG(2,q) graph over prime powers q with spare degree s = d-q-1 >= 1."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, S, pl, lp)
        if best is None or n > best[0]:
            best = (n, E)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D < 3:
        return fallback

    best = fallback

    def consider(n, E):
        nonlocal best
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, E)

    starts = []
    arc = _arc_base(d, random.Random(seed * 7919 + d), start + 0.1 * budget)
    if arc is not None:
        starts.append(arc)
    q = _prime_power_at_most(d - 1)
    if q is not None:
        starts.append(lib.projective_plane_incidence(q))

    valid_starts = []
    for n0, E0 in starts:
        if lib.is_valid(n0, E0, d, D):
            consider(n0, E0)
            valid_starts.append((n0, E0))
    valid_starts.sort(key=lambda t: -t[0])

    for i, (n0, E0) in enumerate(valid_starts):
        now = time.monotonic()
        if now >= deadline:
            break
        sub = now + (deadline - now) / (len(valid_starts) - i)
        res = _search(n0, E0, d, D, sub, random.Random(seed * 131 + i))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
