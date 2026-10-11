import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc-extension (diameter 3).
#
# PG(2, q) incidence, q + 1 <= d. Spare degree s = d - q - 1 on each vertex.
# Adding an A-vertex per point of S (joined to its q+1 lines) and a B-vertex
# per line of S (joined to its q+1 points) keeps diameter 3 whenever every
# line holds <= s points of S and every point lies on <= s lines of S.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Iterated local search for a large S with all loads <= s, starting from feasible S0."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return (n, edges) candidates for prime powers q with q + 1 <= d."""
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
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generic helpers.
# ----------------------------------------------------------------------------

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


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D, from adjacency sets/lists."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Bold new family: annealed extension by two vertices.
#
# Starting from a valid graph, add one side-0 vertex and one side-1 vertex
# (isolated), then anneal over cross-edge moves: add an edge between
# deficient vertices, delete an edge, or perform a degree-preserving
# 2-switch. The cost is the number of pairs at distance > D. Success means
# cost 0 with max degree <= d. Bipartiteness holds by construction, since
# every edge joins colour 0 to colour 1.
# ----------------------------------------------------------------------------

def _sa_extend(n, edges, colors, d, D, rng, deadline):
    """Try to add two vertices (colours 0 and 1) with annealing. Returns (n2, E, colors) or None."""
    n2 = n + 2
    col = list(colors) + [0, 1]
    adj = [set() for _ in range(n2)]
    E = []
    for u, v in edges:
        a, b = (u, v) if col[u] == 0 else (v, u)
        if b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
    cost = _bad(n2, adj, D)
    if cost == 0:
        return n2, E, col

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0 and time.monotonic() < deadline:
        T = 0.8 * (0.02 ** ((time.monotonic() - t0) / span))
        side0 = [v for v in range(n2) if col[v] == 0 and len(adj[v]) < d]
        side1 = [v for v in range(n2) if col[v] == 1 and len(adj[v]) < d]
        r = rng.random()
        undo = None
        if r < 0.5 and side0 and side1:
            u = rng.choice(side0)
            v = rng.choice(side1)
            if v in adj[u]:
                continue
            adj[u].add(v)
            adj[v].add(u)
            E.append((u, v))
            undo = ("add", u, v)
        elif r < 0.65 and E:
            i = rng.randrange(len(E))
            u, v = E[i]
            E[i] = E[-1]
            E.pop()
            adj[u].discard(v)
            adj[v].discard(u)
            undo = ("rem", u, v)
        elif len(E) >= 2:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(e)
            adj[e].add(a)
            adj[c].add(b)
            adj[b].add(c)
            E[i] = (a, e)
            E[j] = (c, b)
            undo = ("sw", i, j, a, b, c, e)
        else:
            continue

        c2 = _bad(n2, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            kind = undo[0]
            if kind == "add":
                _, u, v = undo
                E.pop()
                adj[u].discard(v)
                adj[v].discard(u)
            elif kind == "rem":
                _, u, v = undo
                E.append((u, v))
                adj[u].add(v)
                adj[v].add(u)
            else:
                _, i, j, a, b, c, e = undo
                adj[a].discard(e)
                adj[e].discard(a)
                adj[c].discard(b)
                adj[b].discard(c)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)
                E[i] = (a, b)
                E[j] = (c, e)

    if cost == 0:
        return n2, list(E), col
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Base: PG(2, q) incidence, then arc-extension for extra vertices.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d), best_n):
            consider(n_c, e_c)

    # Annealed two-vertex growth from the best valid graph found so far.
    # Skipped when the graph already meets the Moore bound (e.g. calibration cases).
    if best_n < lib.moore_bound(d, D):
        n_cur, e_cur = best
        adj0 = [[] for _ in range(n_cur)]
        for u, v in e_cur:
            adj0[u].append(v)
            adj0[v].append(u)
        colors = _bipartition(n_cur, adj0)
        while time.monotonic() < deadline:
            res = _sa_extend(n_cur, e_cur, colors, d, D, rng, deadline)
            if res is None:
                break
            n2, e2, c2 = res
            if not lib.is_valid(n2, e2, d, D):
                break
            n_cur, e_cur, colors = n2, e2, c2
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
