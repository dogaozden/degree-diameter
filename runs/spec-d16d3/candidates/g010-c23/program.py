import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and arc-extended incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (n2, edges, m, point_lines, line_points, pts) for PG(2, q) incidence."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
    return n2, edges, m, point_lines, line_points, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_set(q, pts):
    """Conic (plus nucleus for even q) as point indices."""
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old incidence graph plus an A-vertex per point of S and a B-vertex per S-line."""
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


# ----------------------------------------------------------------------------
# Cover-based growth and saturation (both preserve diameter and bipartiteness).
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _cover(cands, ball, full, cap, rng, randomize):
    """Greedy cover of `full` by at most `cap` candidates; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < cap:
        best_g, best_i = 0, -1
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


def _grow(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods are radius-(D-1) covers of the whole graph."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(8):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen is not None:
                    break
            if chosen is None:
                continue
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour pairs in random order (adds edges only)."""
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    state = {"n": n0, "best": (n0, e0)}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["best"] = (n, e)

    if D >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:4]
        arc_data = {}  # q -> (m, edges, point_lines, line_points, pts, s)
        for q in qs:
            if time.monotonic() > deadline:
                break
            n2, pe, m, pl, lp, pts = _pg_data(q)
            consider(n2, pe)  # plain PG(2,q) incidence, diameter 3
            s = d - q - 1
            if s >= 1:
                arc_data[q] = (m, pe, pl, lp, pts, s)

        # Deterministic arc candidates (conic when it fits, else greedy), grown and saturated.
        for q, (m, pe, pl, lp, pts, s) in arc_data.items():
            if time.monotonic() > deadline:
                break
            cands = []
            if s >= 2:
                cs = _conic_set(q, pts)
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            g = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
            if g and _loads_ok(g, s, m, pl, lp):
                cands.append(g)
            for S in cands:
                n3, e3 = _arc_graph(m, pe, pl, lp, S)
                consider(n3, e3)
                sub_deadline = min(deadline, time.monotonic() + 0.2 * (deadline - start))
                n4, e4 = _grow(n3, e3, d, D, sub_deadline, rng)
                e4 = _saturate(n4, e4, d, rng)
                consider(n4, e4)

        # Remaining time: randomized arc restarts followed by growth and saturation.
        keys = list(arc_data.keys())
        while keys and time.monotonic() < deadline:
            q = rng.choice(keys)
            m, pe, pl, lp, pts, s = arc_data[q]
            S = _greedy_arc(m, s, pl, lp, rng, 3, deadline)
            if not S or not _loads_ok(S, s, m, pl, lp):
                continue
            n3, e3 = _arc_graph(m, pe, pl, lp, S)
            n4, e4 = _grow(n3, e3, d, D, deadline, rng)
            e4 = _saturate(n4, e4, d, rng)
            consider(n4, e4)

    n, e = state["best"]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
