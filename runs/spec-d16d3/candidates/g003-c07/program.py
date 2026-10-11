import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base data.
# ----------------------------------------------------------------------------

def _pg_parts(q):
    """Return (m, edges, point_lines, line_points) for the incidence graph of PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


# ----------------------------------------------------------------------------
# NEW: plateau arc search with block-swap moves.
#
# Items are chosen from 0..m-1. Each group (a line, or a point) may contain at
# most s chosen items. groups_of[x] lists the groups containing item x, and
# members_of[g] lists the items in group g. Moves:
#   - add a free item;
#   - insert an item x that is blocked, dropping all chosen items that block it,
#     then re-adding any dropped item that became free. The move is kept when
#     the size does not decrease (plateau moves), and undone otherwise.
# For points, groups_of = point_lines and members_of = line_points. For lines,
# the roles are swapped. The two searches are independent, because the
# A-vertex load and the B-vertex load do not interact.
# ----------------------------------------------------------------------------

def _arc_search(m, s, groups_of, members_of, rng, deadline, iters):
    load = [0] * len(members_of)
    chosen = [False] * m

    def put(x):
        chosen[x] = True
        for g in groups_of[x]:
            load[g] += 1

    def drop(x):
        chosen[x] = False
        for g in groups_of[x]:
            load[g] -= 1

    def free(x):
        return all(load[g] < s for g in groups_of[x])

    order = list(range(m))
    rng.shuffle(order)
    for x in order:
        if free(x):
            put(x)
    size = sum(chosen)
    best = [i for i in range(m) if chosen[i]]

    for it in range(iters):
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if chosen[x]:
            continue
        if free(x):
            put(x)
            size += 1
            if size > len(best):
                best = [i for i in range(m) if chosen[i]]
            continue
        blk = {y for g in groups_of[x] if load[g] >= s
               for y in members_of[g] if chosen[y]}
        if not blk or len(blk) > 3 * s:
            continue
        old = list(blk)
        for y in old:
            drop(y)
        put(x)
        rng.shuffle(old)
        readded = []
        for y in old:
            if free(y):
                put(y)
                readded.append(y)
        change = 1 + len(readded) - len(old)
        if change >= 0:
            size += change
            if size > len(best):
                best = [i for i in range(m) if chosen[i]]
        else:
            for y in readded:
                drop(y)
            drop(x)
            for y in old:
                put(y)
    return best


def _arc_graph(m, edges, point_lines, line_points, S, T):
    """PG(2,q) incidence plus an A-vertex per point of S (on the point side)
    and a B-vertex per line of T (on the line side). Diameter stays 3 for any S, T."""
    n = 2 * m + len(S) + len(T)
    E = list(edges)
    base_a = 2 * m
    for t, P in enumerate(S):
        x = base_a + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = base_a + len(S)
    for t, L in enumerate(T):
        y = base_b + t
        for X in line_points[L]:
            E.append((X, y))
    return n, E


# ----------------------------------------------------------------------------
# Cover-based growth and saturation (diameter-preserving).
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
    """Add vertices whose neighbourhoods cover all vertices within D-1 (keeps diameter <= D)."""
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
            for attempt in range(120):
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
    """Join deficient opposite-side vertices with spare degree (adding edges never breaks diameter)."""
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
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
        qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)
        live = [q for q in qs if d - q - 1 >= 1]
        pending = len(live)
        for q in qs:
            if time.monotonic() > end:
                break
            m, edges, point_lines, line_points = _pg_parts(q)
            consider(2 * m, edges)
            s = d - q - 1
            if s < 1:
                continue
            # Equal share of the remaining time for each live q.
            per = (end - time.monotonic()) / max(1, pending)
            pending -= 1
            t0 = time.monotonic()
            # Independent point-set S (A-vertices) and line-set T (B-vertices).
            S = _arc_search(m, s, point_lines, line_points, rng,
                            t0 + 0.3 * per, 400000)
            T = _arc_search(m, s, line_points, point_lines, rng,
                            t0 + 0.6 * per, 400000)
            n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S, T)
            consider(n_c, e_c)
            # Diameter-preserving growth with the leftover spare degree.
            gn, ge = _grow(n_c, e_c, d, D, t0 + per, rng)
            consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
