"""Flag-duplication construction for bipartite diameter-3 graphs.

Base: incidence graph of PG(2, q), q the largest prime power with q + 1 <= d, so each
vertex has spare capacity s = d - q - 1.

Flag gadget: choose a flag (P, L), with P a point on the line L. Add a new point-side
vertex A adjacent to the q lines through P other than L, and a new line-side vertex B
adjacent to the q points of L other than P, plus the edge A-B. Each gadget adds 2
vertices and uses one unit of spare on each of those lines and points.

Diameter 3 for a bipartite graph holds iff any two same-side vertices share a neighbour.
The gadgets satisfy this except for a few pairs, which are repaired by adding edges
that use leftover spare degree. Every candidate is checked with lib.is_valid.

The oval extension (conic plus nucleus) is kept as a fast baseline.
"""
import random
import time

import lib


def _best_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for the incidence graph of PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _oval_graph(q, d, m, edges, point_lines, line_points):
    """Oval extension: an A-vertex per oval point (on its pencil) and a B-vertex per oval line.

    Returns (n, E), or None if some vertex would exceed degree d.
    """
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    s = d - q - 1
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
    for j in S:
        for X in line_points[j]:
            cp[X] += 1
    if max(cl) > s or max(cp) > s:
        return None
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        A = 2 * m + t
        for L in point_lines[P]:
            E.append((A, m + L))
    for t, j in enumerate(S):
        B = 2 * m + k + t
        for X in line_points[j]:
            E.append((X, B))
    return n, E


def _greedy_flags(m, point_lines, line_points, s, rng, max_pen):
    """Random greedy choice of flags (P, L) with line loads <= s and point loads <= s.

    max_pen bounds the number of conflicts (pairs needing repair) a new flag may create.
    """
    lload = [0] * m       # number of A-vertices attached to each old line
    pload = [0] * m       # number of B-vertices attached to each old point
    centers_on = [0] * m  # number of chosen centres on each line
    inl = [0] * m         # number of chosen missing-lines through each point
    is_center = [False] * m
    cands = [(P, L) for P in range(m) for L in point_lines[P]]
    rng.shuffle(cands)
    flags = []
    for P, L in cands:
        if is_center[P]:
            continue
        if centers_on[L] + inl[P] > max_pen:
            continue
        lines_use = [M for M in point_lines[P] if M != L]
        if any(lload[M] >= s for M in lines_use):
            continue
        pts_use = [X for X in line_points[L] if X != P]
        if any(pload[X] >= s for X in pts_use):
            continue
        is_center[P] = True
        for M in point_lines[P]:
            centers_on[M] += 1
        for M in lines_use:
            lload[M] += 1
        for X in pts_use:
            pload[X] += 1
        for X in line_points[L]:
            inl[X] += 1
        flags.append((P, L))
    return flags


def _assemble(m, edges, point_lines, line_points, flags):
    """Build (n, E) from the PG base and the flag gadgets."""
    f = len(flags)
    E = list(edges)
    for i, (P, L) in enumerate(flags):
        A = 2 * m + i
        B = 2 * m + f + i
        for M in point_lines[P]:
            if M != L:
                E.append((A, m + M))
        E.append((A, B))
        for X in line_points[L]:
            if X != P:
                E.append((X, B))
    return 2 * m + 2 * f, E


def _repair(n, E, m, f, d, rng):
    """Add edges using spare degree so that same-side vertices share a neighbour.

    Returns (ok, adj, bad), where bad holds new vertices that could not be fixed.
    """
    base = 2 * m
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    nbm = [0] * n
    for v in range(n):
        x = 0
        for u in adj[v]:
            x |= 1 << u
        nbm[v] = x
    side = [0 if (v < m or base <= v < base + f) else 1 for v in range(n)]
    members = ([v for v in range(n) if side[v] == 0],
               [v for v in range(n) if side[v] == 1])
    while True:
        viol = []
        for x in range(base, n):
            for y in members[side[x]]:
                if y == x or (base <= y < x):
                    continue
                if not (nbm[x] & nbm[y]):
                    viol.append((x, y))
        if not viol:
            return True, adj, set()
        rng.shuffle(viol)
        progress = False
        bad = set()
        for x, y in viol:
            if nbm[x] & nbm[y]:
                continue
            done = False
            for a, b in ((x, y), (y, x)):
                if len(adj[a]) >= d:
                    continue
                cands = [z for z in adj[b]
                         if z != a and z not in adj[a] and len(adj[z]) < d]
                if cands:
                    z = rng.choice(cands)
                    adj[a].add(z)
                    adj[z].add(a)
                    nbm[a] |= 1 << z
                    nbm[z] |= 1 << a
                    done = True
                    break
            if done:
                progress = True
            else:
                bad.add(x)
        if not progress:
            return False, adj, bad


def _flag_search(d, D, q, m, edges, point_lines, line_points, deadline, rng, best):
    """Randomised restarts: greedy flags, repair, drop blamed flags, verify, keep the best."""
    s = d - q - 1
    while time.monotonic() < deadline:
        max_pen = rng.choice((0, 0, 1, 2, 3, 5))
        flags = _greedy_flags(m, point_lines, line_points, s, rng, max_pen)
        while flags and 2 * m + 2 * len(flags) > best[0]:
            if time.monotonic() >= deadline:
                return best
            n, E = _assemble(m, edges, point_lines, line_points, flags)
            ok, adj, bad = _repair(n, E, m, len(flags), d, rng)
            if ok:
                E2 = [(u, v) for u in range(n) for v in adj[u] if u < v]
                if lib.is_valid(n, E2, d, D):
                    best = (n, E2)
                break
            if not bad:
                break
            x = rng.choice(sorted(bad))
            flags.pop((x - 2 * m) % len(flags))
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a valid fallback for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    q = _best_q(d)
    if q is None:
        return best

    m, edges, point_lines, line_points = _pg_data(q)
    cand = (2 * m, list(edges))
    if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    s = d - q - 1
    if s >= 2:
        og = _oval_graph(q, d, m, edges, point_lines, line_points)
        if og is not None and og[0] > best[0] and lib.is_valid(og[0], og[1], d, D):
            best = og

    if s >= 1:
        best = _flag_search(d, D, q, m, edges, point_lines, line_points,
                            deadline, rng, best)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
