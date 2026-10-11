"""Bipartite graphs of diameter 3 from PG(2,q) with independent capped point and line sets.

New in this version:
  * Independent "NA" and "NB" families. NA_p (one per chosen point p) is joined to the q+1
    lines through p. NB_l (one per chosen line l) is joined to the q+1 points on l. The two
    chosen sets are picked independently, so each family is a separate capped set problem.
  * _capped_set: a plateau local search for a largest family of elements whose members hit
    each target at most `cap` times. It is seeded with the conic (an arc) when that is feasible.
  * A family scan over every prime power q with q+1 <= d, keeping the largest valid graph.
  * Cover growth (parent's idea, rewritten): adds a vertex whose neighbourhood 2-covers the
    opposite side, then checks the result with lib.is_valid.

Within the q = 13, d = 16 family, every point and line has spare degree 2 and the chosen sets
must be arcs (dual arcs for NB), so their size is capped at q + 1 = 14. That gives 2*183 + 28 =
394. The search checks this family but cannot exceed that cap.
"""
import random
import time

import lib


def _pg_parts(q):
    """Return (m, point_lines, line_points) for PG(2, q); points and lines are both 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


def _conic(q):
    """Conic (plus nucleus for even q) as indices into lib.projective_points(q)."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _capped_set(members, n_targets, cap, rng, deadline, iters, init):
    """Largest family of elements found by local search, with every target hit at most `cap` times.

    members[e] lists the targets of element e. The search starts from `init` (kept when it is
    feasible), then adds elements greedily. Plateau moves swap one blocking element out for a
    new one. Returns the chosen element indices.
    """
    m = len(members)
    cnt = [0] * n_targets
    owners = [[] for _ in range(n_targets)]
    inS = [False] * m
    size = 0

    def add(e):
        nonlocal size
        inS[e] = True
        size += 1
        for t in members[e]:
            cnt[t] += 1
            owners[t].append(e)

    def remove(e):
        nonlocal size
        inS[e] = False
        size -= 1
        for t in members[e]:
            cnt[t] -= 1
            owners[t].remove(e)

    rest = list(range(m))
    rng.shuffle(rest)
    for e in list(init) + rest:
        if not inS[e] and all(cnt[t] < cap for t in members[e]):
            add(e)
    best = [e for e in range(m) if inS[e]]

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        e = rng.randrange(m)
        if inS[e]:
            continue
        blockers = set()
        for t in members[e]:
            if cnt[t] >= cap:
                blockers.update(owners[t])
                if len(blockers) > 1:
                    break
        if not blockers:
            add(e)
        elif len(blockers) == 1 and rng.random() < 0.3:
            (f,) = blockers
            remove(f)
            add(e)
        else:
            continue
        if size > len(best):
            best = [x for x in range(m) if inS[x]]
    return best


def _plane_extension(q, d, rng, deadline):
    """PG(2,q) incidence plus independent NA and NB families, each with per-vertex cap s = d - q - 1."""
    s = d - q - 1
    m, point_lines, line_points = _pg_parts(q)
    n = 2 * m
    edges = []
    for p in range(m):
        for L in point_lines[p]:
            edges.append((p, m + L))
    if s <= 0:
        return n, edges
    conic = _conic(q)
    # NA: chosen points, each line may contain at most s of them.
    P = _capped_set(point_lines, m, s, rng, deadline, 20000, conic)
    # NB: chosen lines, each point may lie on at most s of them.
    Lam = _capped_set(line_points, m, s, rng, deadline, 20000, conic)
    for p in P:
        for L in point_lines[p]:
            edges.append((n, m + L))
        n += 1
    for L in Lam:
        for p in line_points[L]:
            edges.append((p, n))
        n += 1
    return n, edges


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


def _colour(n, adj):
    """Two-colouring of a bipartite graph."""
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


def _cover(pool, ball, full, d, rng, shuffle):
    """Greedy cover of `full` by at most d candidates from pool; None if it fails."""
    pool = list(pool)
    if shuffle:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best, bg = None, 0
        for s in pool:
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                best, bg = s, g
        if best is None:
            break
        chosen.append(best)
        pool.remove(best)
        covered |= ball[best]
    return chosen if covered == full else None


def _grow_cover(n, edges, d, D, rng, deadline, max_add=60):
    """Repeatedly add a vertex whose neighbours cover all vertices within D-1 of the opposite side."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _colour(n, adj)
    added = 0
    while added < max_add and time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        grown = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            chosen = None
            for attempt in range(4):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                grown = True
                added += 1
                break
        if not grown:
            break
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    hard = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid whenever D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return best

    # Family scan over prime powers q with q + 1 <= d (diameter 3 from PG(2, q) incidence).
    scan_deadline = start + 0.5 * time_limit
    for q in range(2, d):
        if not lib.is_prime_power(q) or time.monotonic() > scan_deadline:
            continue
        n, e = _plane_extension(q, d, rng, scan_deadline)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Cover growth on the best graph found so far.
    n2, e2 = _grow_cover(best[0], best[1], d, D, rng, hard)
    if n2 > best[0] and lib.is_valid(n2, e2, d, D):
        best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
