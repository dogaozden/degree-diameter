import random
import time

import lib

# New in this version: the A-side and B-side sets of the arc extension are chosen
# independently, each as a random projective image of a conic (or hyperoval for even q),
# then greedily filled to the load bound. Every candidate is then grown by diameter-safe
# cover extension and edge saturation, and the result is checked with lib.is_valid.


def _pg_tables(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
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


def _rand_matrix(F, rng):
    """Random invertible 3x3 matrix over GF(q)."""
    while True:
        M = [[rng.randrange(F.q) for _ in range(3)] for _ in range(3)]
        (a, b, c), (x, y, z), (u, v, w) = M
        det = F.add(
            F.sub(F.mul(a, F.sub(F.mul(y, w), F.mul(z, v))),
                  F.mul(b, F.sub(F.mul(x, w), F.mul(z, u)))),
            F.mul(c, F.sub(F.mul(x, v), F.mul(y, u))),
        )
        if det:
            return M


def _apply(F, M, v):
    """Projective image of point vector v under M, normalised so the first nonzero entry is 1."""
    out = []
    for row in M:
        s = 0
        for j in range(3):
            s = F.add(s, F.mul(row[j], v[j]))
        out.append(s)
    c = next(x for x in out if x)
    inv = F.inv(c)
    return tuple(F.mul(inv, x) for x in out)


def _conic_vectors(q, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    vecs = [(1, t, F.mul(t, t)) for t in range(q)]
    vecs.append((0, 0, 1))
    if q % 2 == 0:
        vecs.append((0, 1, 0))
    return vecs


def _fill(m, s, loads, base, rng, trials, deadline):
    """Largest set S of indices with every load counter <= s.

    Start from the base set (keeping only the elements that fit), then add the
    remaining indices in random order. Several random orders are tried.
    """
    best = []
    order = list(range(m))
    for _ in range(trials):
        if best and time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        inS = [False] * m
        S = []
        for P in list(base) + order:
            if inS[P]:
                continue
            if all(cnt[L] < s for L in loads[P]):
                S.append(P)
                inS[P] = True
                for L in loads[P]:
                    cnt[L] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus an A-vertex per point of SA and a B-vertex per line of SB."""
    ka, kb = len(SA), len(SB)
    n = 2 * m + ka + kb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + ka + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=30):
    """Add vertices whose neighbourhoods cover all vertices within D-1 (diameter-safe)."""
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices (never increases distances)."""
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
    """Alternate cover extension and saturation while progress is made."""
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


def _arc_search(d, D, rng, deadline, consider):
    """Repeatedly build randomized two-sided arc extensions of PG(2, q) and grow them."""
    qs = [q for q in range(min(d - 1, 23), 1, -1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    if not qs:
        return
    tables = {}
    while time.monotonic() < deadline:
        q = qs[0] if (len(qs) == 1 or rng.random() < 0.6) else rng.choice(qs)
        if q not in tables:
            F = lib.GF(q)
            m, edges, pl, lp, index = _pg_tables(q)
            tables[q] = (F, m, edges, pl, lp, index)
        F, m, edges, pl, lp, index = tables[q]
        s = d - q - 1
        vecs = _conic_vectors(q, F)
        ident = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
        if rng.random() < 0.3:
            MA = ident
            MB = ident
        else:
            MA = _rand_matrix(F, rng)
            MB = _rand_matrix(F, rng)
        base_a = [index[_apply(F, MA, v)] for v in vecs]
        base_b = [index[_apply(F, MB, v)] for v in vecs]
        SA = _fill(m, s, pl, base_a, rng, 3, deadline)
        SB = _fill(m, s, lp, base_b, rng, 3, deadline)
        n, e = _arc_graph(m, edges, pl, lp, SA, SB)
        n, e = _grow(n, e, d, D, deadline, rng)
        consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    state = {"n": 2 * d, "e": lib.haar_graph(d, range(d))[1]}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e

    if D == 2:
        return state["n"], state["e"]

    # Plain projective plane with the largest prime power q <= d - 1, grown by covers.
    try:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)
    except Exception:
        pass

    # Two-sided randomized arc extensions (main search for D = 3).
    try:
        _arc_search(d, D, rng, deadline, consider)
    except Exception:
        pass

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
