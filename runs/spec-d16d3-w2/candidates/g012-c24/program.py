import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q): points 0..m-1, lines
# m..2m-1. Every old vertex has degree q+1, so with d >= q+1 it has spare
# capacity s = d-q-1. An "A-vertex" for a point P joins the q+1 lines through P;
# a "B-vertex" for a line j joins the q+1 points on j. Both kinds stay within
# distance 3 of everything, and the only limit is that each old vertex receives
# at most s new edges. Choosing the point set S for A-vertices (and line set for
# B-vertices) as a (k, s)-arc gives order 2(q^2+q+1) + 2|S|.
# ----------------------------------------------------------------------------

def _pg(q):
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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s A-points and every point lies on <= s B-lines."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy arc S (same index used for A-points and B-lines)."""
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


def _conic(q, index):
    """Conic (plus nucleus for even q) as a point-index set."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _edges(adj):
    return [(u, v) for u in adj for v in adj[u] if u < v]


def _copy(adj):
    return {v: set(s) for v, s in adj.items()}


def _restore(adj, src):
    adj.clear()
    for v, s in src.items():
        adj[v] = set(s)


def _add_star(adj, x, nb):
    adj[x] = set(nb)
    for u in nb:
        adj[u].add(x)


def _drop(adj, x):
    for u in adj.pop(x):
        adj[u].discard(x)


def _check(adj, d, D):
    n, E = lib.relabel(_edges(adj))
    return lib.is_valid(n, E, d, D)


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q+1 <= d, build the arc-extended graph as an adjacency dict."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index = _pg(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic(q, index)
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            S = []
        adj = {}

        def link(u, v):
            adj.setdefault(u, set()).add(v)
            adj.setdefault(v, set()).add(u)

        for u, v in edges:
            link(u, v)
        k = len(S)
        for t, P in enumerate(S):
            for L in pl[P]:
                link(2 * m + t, m + L)
        for t, j in enumerate(S):
            for Q in lp[j]:
                link(2 * m + k + t, Q)
        out.append((len(adj), adj, 2 * m + 2 * k, m, pl, lp))
    return out


# ----------------------------------------------------------------------------
# New helper: star regrowth + validated remove/regrow search.
#
# A new side-0 vertex is admissible (for D = 3) essentially only as a full
# pencil of q+1 lines through one point, and a new side-1 vertex as the points
# of one line. _regrow tries every such star in random order, keeping only the
# ones that keep the graph valid. _search repeatedly removes one random added
# vertex and regrows, keeping the best valid graph seen.
# ----------------------------------------------------------------------------

def _regrow(adj, nxt, m, pl, lp, d, D, rng, deadline):
    cands = [(0, P) for P in range(m)] + [(1, j) for j in range(m)]
    rng.shuffle(cands)
    for kind, i in cands:
        if time.monotonic() > deadline:
            break
        nb = [m + L for L in pl[i]] if kind == 0 else list(lp[i])
        if any(len(adj[u]) >= d for u in nb):
            continue
        x = nxt
        _add_star(adj, x, nb)
        if _check(adj, d, D):
            nxt += 1
        else:
            _drop(adj, x)
    return nxt


def _search(adj, nxt, m, pl, lp, d, D, deadline, rng):
    best = _copy(adj)
    best_cnt = len(adj)
    while time.monotonic() < deadline:
        snap = _copy(adj)
        news = [v for v in adj if v >= 2 * m]
        if news:
            x = rng.choice(news)
            _drop(adj, x)
            if not _check(adj, d, D):
                _restore(adj, snap)
                continue
        nxt = _regrow(adj, nxt, m, pl, lp, d, D, rng, deadline)
        if len(adj) > best_cnt:
            best = _copy(adj)
            best_cnt = len(adj)
        elif len(adj) < best_cnt and rng.random() < 0.5:
            _restore(adj, best)
            nxt = max(best) + 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        cands = _arc_candidates(d, start + 0.3 * time_limit, rng)
        cands.sort(key=lambda t: -t[0])
        for c in cands[:3]:
            consider(*lib.relabel(_edges(c[1])))

        if D == 3 and cands:
            cnt, adj, nxt, m, pl, lp = cands[0]
            if _check(adj, d, D):
                best_adj = _search(adj, nxt, m, pl, lp, d, D, deadline, rng)
                consider(*lib.relabel(_edges(best_adj)))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
