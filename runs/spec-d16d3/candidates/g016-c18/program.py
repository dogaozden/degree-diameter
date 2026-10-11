import random
import time

import lib


def _best_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_struct(q):
    """Incidence graph of PG(2, q) plus point->lines and line->points lists."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic(q):
    """Conic (plus nucleus for even q) as point indices. It is an arc: <= 2 points on any line.

    Lines share the point vectors, so this same set is also an arc when used as line indices.
    """
    pts = lib.projective_points(q)
    idx = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [idx[(1, t, F.mul(t, t))] for t in range(q)] + [idx[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(idx[(0, 1, 0)])
    return S


def _random_arc(cover, m, s, rng):
    """Random greedy set S of elements such that every target is covered at most s times.

    cover[e] lists the targets hit by element e. Used for S_P (targets = lines)
    and for S_L (targets = points).
    """
    order = list(range(m))
    rng.shuffle(order)
    load = [0] * m
    S = []
    for e in order:
        c = cover[e]
        if all(load[t] < s for t in c):
            S.append(e)
            for t in c:
                load[t] += 1
    return S


def _pick(rng, conic, cover, m, s):
    """Either a random subset of the conic (always an arc) or a fresh random greedy arc."""
    if conic and rng.random() < 0.4:
        k = rng.randint(max(1, len(conic) - 4), len(conic))
        return rng.sample(conic, k)
    return _random_arc(cover, m, s, rng)


def _base(m, edges, PL, LP, SP, SL):
    """PG(2,q) incidence plus an A-vertex per point of SP and a B-vertex per line of SL.

    A_P is joined to the q+1 lines through P (point side). B_L is joined to the q+1 points of L
    (line side). Diameter stays <= 3 for any SP, SL. Degrees: a line gets #SP extra edges,
    a point gets #SL extra edges.
    """
    kP = len(SP)
    n = 2 * m + kP + len(SL)
    E = list(edges)
    for t, P in enumerate(SP):
        a = 2 * m + t
        for L in PL[P]:
            E.append((a, m + L))
    for t, L in enumerate(SL):
        b = 2 * m + kP + t
        for Q in LP[L]:
            E.append((Q, b))
    return n, E


def _clone_pack(n, E, d, rng):
    """Repeatedly add twin clones: a new vertex with the same neighbourhood as an existing vertex.

    A twin never increases any distance among old vertices: its distance to any other vertex w
    equals the distance of the original vertex it copies, and it is at distance 2 from that
    original. So diameter is preserved. Bipartiteness is preserved (the clone sits on the same
    side). A clone is allowed only when every neighbour of the copied vertex has spare degree.
    """
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    while True:
        cands = []
        for x in range(n):
            nb = adj[x]
            if nb and len(nb) <= d and all(len(adj[y]) < d for y in nb):
                cands.append(x)
        if not cands:
            break
        if rng.random() < 0.3:
            pool = cands
        else:
            best_deg = min(len(adj[x]) for x in cands)
            pool = [x for x in cands if len(adj[x]) == best_deg]
        x = rng.choice(pool)
        nb = list(adj[x])
        v = n
        n += 1
        adj.append(set(nb))
        for y in nb:
            adj[y].add(v)
    E2 = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, E2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2: a safe fallback whenever D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, E)

    q = _best_q(d)
    if D < 3 or q is None:
        return best

    m, edges, PL, LP = _pg_struct(q)
    s = d - q - 1
    moore = lib._moore_bound(d, D)

    # Plain PG(2,q) incidence graph (diameter 3, degree q+1).
    consider(2 * m, list(edges))
    conic = _conic(q) if s >= 2 else []

    # Search: choose the arc-like sets SP and SL, add A/B vertices,
    # then pack twin clones into the remaining spare degree.
    while time.monotonic() < deadline and best[0] < moore:
        if s == 0:
            SP, SL = [], []
        else:
            SP = _pick(rng, conic, PL, m, s)
            SL = _pick(rng, conic, LP, m, s)
        n, E = _base(m, edges, PL, LP, SP, SL)
        consider(n, E)
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            n2, E2 = _clone_pack(n, E, d, rng)
            consider(n2, E2)

    return best
