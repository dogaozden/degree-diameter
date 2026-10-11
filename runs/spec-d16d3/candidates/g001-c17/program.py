"""Diameter-3 bipartite construction: PG(2,q) plus independent arc-based side vertices, then cover growth."""
import random
import time

import lib


def _pg(q):
    """Incidence graph of PG(2,q) with its point/line adjacency lists and an optional conic seed."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    conic = None
    if q >= 3:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(pts)}
        conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            conic.append(index[(0, 1, 0)])
    return m, edges, point_lines, line_points, conic


def _pack(m, s, touch, rng, init, iters, deadline):
    """Find a large set X of elements such that each constraint id is touched by at most s members.

    touch[x] lists the constraint ids element x touches. Greedy fill, then plateau swaps.
    """
    byc = [set() for _ in range(m)]
    mem = set()

    def add(x):
        mem.add(x)
        for c in touch[x]:
            byc[c].add(x)

    def rem(x):
        mem.discard(x)
        for c in touch[x]:
            byc[c].discard(x)

    def free(x):
        return all(len(byc[c]) < s for c in touch[x])

    for x in list(init) + rng.sample(range(m), m):
        if x not in mem and free(x):
            add(x)
    best = set(mem)
    for it in range(iters):
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if x in mem:
            continue
        blocked = [c for c in touch[x] if len(byc[c]) >= s]
        if not blocked:
            add(x)
        else:
            removed = []
            for c in blocked:
                if len(byc[c]) >= s:
                    y = rng.choice(sorted(byc[c]))
                    rem(y)
                    removed.append(y)
            if free(x) and (len(removed) == 1 or rng.random() < 0.05):
                add(x)
            else:
                for y in removed:
                    add(y)
        if len(mem) > len(best):
            best = set(mem)
    return sorted(best)


def _assemble(m, edges, point_lines, line_points, S, T):
    """Add an A-vertex per point of S (joined to its lines) and a B-vertex per line of T (joined to its points)."""
    n = 2 * m + len(S) + len(T)
    E = list(edges)
    a0 = 2 * m
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((a0 + t, m + L))
    b0 = a0 + len(S)
    for t, L in enumerate(T):
        for Q in line_points[L]:
            E.append((Q, b0 + t))
    return n, E


def _adj(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] >= 0:
            continue
        color[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] < 0:
                    color[v] = 1 - color[u]
                    st.append(v)
    return color


def _balls(n, adj, r):
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


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate neighbourhoods; None on failure."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, E, d, D, deadline, rng):
    """Add vertices whose neighbourhoods reach every vertex within D-1 (keeps diameter <= D)."""
    E = list(E)
    adj = _adj(n, E)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [x for x in range(n) if color[x] == c and deg[x] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(10):
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen or time.monotonic() >= deadline:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    E.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, E


def _saturate(n, E, d, rng):
    """Join spare-degree opposite-side pairs (only shrinks distances, so validity is kept)."""
    adj = _adj(n, E)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    have = {(min(u, v), max(u, v)) for u, v in E}
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in have]
    rng.shuffle(pairs)
    out = list(E)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _grow(n, E, d, D, deadline, rng):
    cur_n, cur_e = n, list(E)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    if D == 2:
        return state["best"]

    rng = random.Random(seed)
    cfgs = []
    for q in range(2, min(d - 1, 23) + 1):
        if lib.is_prime_power(q):
            cfgs.append((q, d - q - 1))

    structs = {}

    def struct(q):
        if q not in structs:
            structs[q] = _pg(q)
        return structs[q]

    # Pass 1: deterministic-ish candidates for every prime power q.
    best_cfg, best_size = None, -1
    for q, s in cfgs:
        if time.monotonic() > deadline:
            break
        m, edges, pl, lp, conic = struct(q)
        consider(2 * m, edges)
        if s < 1:
            continue
        S = _pack(m, s, pl, rng, conic or [], 2000, deadline)
        T = _pack(m, s, lp, rng, conic or [], 2000, deadline)
        n, E = _assemble(m, edges, pl, lp, S, T)
        consider(n, E)
        consider(n, _saturate(n, E, d, rng))
        if n > best_size:
            best_size, best_cfg = n, (q, s)

    # Pass 2: randomized restarts with cover growth, focused on the best configuration.
    work = [(q, s) for q, s in cfgs if s >= 1]
    if work and best_cfg is not None:
        while time.monotonic() < deadline:
            if rng.random() < 0.7:
                q, s = best_cfg
            else:
                q, s = rng.choice(work)
            m, edges, pl, lp, conic = struct(q)
            init = conic if (conic and rng.random() < 0.5) else []
            S = _pack(m, s, pl, rng, init, 3000, deadline)
            T = _pack(m, s, lp, rng, init, 3000, deadline)
            n, E = _assemble(m, edges, pl, lp, S, T)
            E = _saturate(n, E, d, rng)
            consider(n, E)
            n2, E2 = _grow(n, E, d, D, deadline, rng)
            consider(n2, E2)

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
