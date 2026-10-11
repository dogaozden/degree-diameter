import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex (pencil through it)
    and a B-vertex (joined to the points of the dual line). Returns (n, edges, side)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Adjacency + distance bookkeeping
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad(n, adj, D):
    """Number of ORDERED pairs at distance > D (0 iff diameter <= D, given the bipartite setting)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return n * n - sum(r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# New helper: pair-growth by annealing only the NEW vertices' edges.
#
# The base graph is kept frozen. Two fresh vertices x (side 0) and y (side 1)
# are appended. Their edges are the only thing that changes: each move adds,
# removes or swaps one edge incident to x or y, subject to degree <= d on
# both endpoints. Adding edges can never increase the bad-pair count, so the
# search is a restricted, cheap form of repair that never disturbs the base
# structure. A success means the base graph plus one extra bipartite pair
# (x, y) still has diameter <= D.
#
# Slack analysis (why this is worth trying): in the conic-extended PG(2,13)
# graph, many lines and points still have spare degree, so a new vertex has
# free slots to cover the plane with.
# ----------------------------------------------------------------------------

def _grow_pair(n, adj, side, d, D, rng, deadline):
    """Anneal edges incident to the two new vertices n-2 (side 0) and n-1 (side 1).
    Returns True if the whole graph reaches diameter <= D."""
    x, y = n - 2, n - 1
    cost = _bad(n, adj, D)
    T = 3.0
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        z = x if rng.random() < 0.5 else y
        T = max(0.3, T * 0.999)
        opp = [v for v in range(n)
               if side[v] != side[z] and v not in adj[z] and len(adj[v]) < d]
        if len(adj[z]) < d and opp and (not adj[z] or rng.random() < 0.6):
            # Greedy-sampled add: try a few candidate endpoints, keep the best.
            sample = rng.sample(opp, min(4, len(opp)))
            best_c, best_w = None, None
            for w in sample:
                adj[z].add(w)
                adj[w].add(z)
                c = _bad(n, adj, D)
                adj[z].discard(w)
                adj[w].discard(z)
                if best_c is None or c < best_c:
                    best_c, best_w = c, w
            if best_c <= cost or rng.random() < math.exp(-(best_c - cost) / T):
                adj[z].add(best_w)
                adj[best_w].add(z)
                cost = best_c
        elif adj[z]:
            # Swap move: drop one edge, optionally attach to a fresh endpoint.
            w_old = rng.choice(list(adj[z]))
            w_new = rng.choice(opp) if opp else None
            adj[z].discard(w_old)
            adj[w_old].discard(z)
            if w_new is not None:
                adj[z].add(w_new)
                adj[w_new].add(z)
            c = _bad(n, adj, D)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                if w_new is not None:
                    adj[z].discard(w_new)
                    adj[w_new].discard(z)
                adj[z].add(w_old)
                adj[w_old].add(z)
    return True


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), unchanged from parent.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    arc_base = None
    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)
        if cands and lib.is_valid(cands[0][0], cands[0][1], d, D):
            arc_base = cands[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Pair growth for D = 3: repeatedly append one vertex per side and anneal
    # only their edges. Each success becomes the next frozen base.
    if D == 3 and arc_base is not None:
        n, E, side = arc_base
        adj = _to_adj(n, E)
        side = list(side)
        cur_n = n
        while time.monotonic() < deadline:
            n_t = cur_n + 2
            if n_t > _moore(d, D):
                break
            adj.append(set())
            adj.append(set())
            side = side + [0, 1]
            if not _grow_pair(n_t, adj, side, d, D, rng, deadline):
                break
            E2 = [(x, y) for x in range(n_t) for y in adj[x] if x < y]
            if not lib.is_valid(n_t, E2, d, D):
                break
            consider(n_t, E2)
            cur_n = n_t

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
