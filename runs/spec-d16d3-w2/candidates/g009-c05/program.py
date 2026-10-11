import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane with vertex twinning (diameter 3).
#
# Base graph: incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1), plus
# for each P in S an A-vertex joined to the q+1 lines through P and a B-vertex
# joined to the q+1 points on line P. S must be an s-arc with s = d-q-1, so
# every old vertex keeps degree <= d.
#
# Twin lemma: a new vertex with the same neighbourhood as an existing vertex
# on the same side keeps the graph bipartite and keeps all distances unchanged
# (d(x,v) = d(P,v) for v != P, and d(x,P) = 2). So we can keep adding twins of
# vertices whose neighbours all have spare degree. The search chooses S by
# local moves and scores each S by how many twins fit greedily.
# ----------------------------------------------------------------------------

def _pg_struct(q):
    """Return (m, point_lines, line_points) for PG(2, q); lines use the same index as points."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


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
    """Randomized greedy s-arc; returns the largest found."""
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


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _base(m, point_lines, line_points, S):
    """Adjacency sets and sides for PG(2,q) incidence plus A/B vertices for each P in S."""
    k = len(S)
    n = 2 * m + 2 * k
    adj = [set() for _ in range(n)]
    side = [0] * m + [1] * m + [0] * k + [1] * k
    for P in range(m):
        for L in point_lines[P]:
            adj[P].add(m + L)
            adj[m + L].add(P)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            adj[a].add(m + L)
            adj[m + L].add(a)
        b = 2 * m + k + t
        for Q in line_points[P]:
            adj[Q].add(b)
            adj[b].add(Q)
    return adj, side


def _fill(adj, side, d, rng, noise):
    """Greedily add twins of vertices whose neighbours all have spare degree."""
    adj = [set(a) for a in adj]
    side = list(side)
    while True:
        order = sorted(range(len(adj)), key=lambda v: len(adj[v]) + noise * rng.random())
        added = False
        for v in order:
            nb = adj[v]
            if not nb:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            new = len(adj)
            nbl = list(nb)
            adj.append(set(nbl))
            side.append(side[v])
            for u in nbl:
                adj[u].add(new)
            added = True
        if not added:
            break
    return adj, side


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _search(q, d, D, rng, deadline, consider):
    """Local search over s-arcs S in PG(2,q), scoring each by the size after twin filling."""
    m, pl, lp = _pg_struct(q)
    s = d - q - 1
    if s < 0 or m == 0:
        return
    if s == 0:
        adj, _ = _base(m, pl, lp, [])
        consider(adj)
        return

    S = []
    if s >= 2:
        F = lib.GF(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = []
        cs = _conic(q, index, F)
        if _loads_ok(cs, s, m, pl, lp):
            cands.append(cs)
        now = time.monotonic()
        cands.append(_greedy_arc(m, s, pl, lp, rng, 25, min(deadline, now + 0.1 * max(0.0, deadline - now))))
        S = max(cands, key=len)

    def score(Sl):
        adj, side = _base(m, pl, lp, Sl)
        adj2, _ = _fill(adj, side, d, rng, 0.9)
        return adj2

    cur = list(S)
    cur_adj = score(cur)
    cur_n = len(cur_adj)
    consider(cur_adj)

    while time.monotonic() < deadline:
        new = list(cur)
        r = rng.random()
        if r < 0.45 or not new:
            p = rng.randrange(m)
            if p in new:
                continue
            new.append(p)
        elif r < 0.7:
            new.pop(rng.randrange(len(new)))
        else:
            p = rng.randrange(m)
            if p in new:
                continue
            new[rng.randrange(len(new))] = p
        if not _loads_ok(new, s, m, pl, lp):
            continue
        adj2 = score(new)
        n2 = len(adj2)
        if n2 >= cur_n or rng.random() < 0.03:
            cur, cur_n, cur_adj = new, n2, adj2
            consider(adj2)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    budget = min(0.8 * float(time_limit), 45.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "E": fb_E}

    def consider(adj):
        n = len(adj)
        if n > best["n"]:
            E = _edges_of(adj)
            if lib.is_valid(n, E, d, D):
                best["n"], best["E"] = n, E

    def store_edges(n, E):
        if n > best["n"] and lib.is_valid(n, E, d, D):
            best["n"], best["E"] = n, list(E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            store_edges(gq[0], gq[1])

    if D >= 3:
        qs = sorted([q for q in range(2, d) if lib.is_prime_power(q)], reverse=True)
        weights = [3.0 if i < 3 else 1.0 for i in range(len(qs))]
        for i, q in enumerate(qs):
            now = time.monotonic()
            rem = deadline - now
            if rem <= 0:
                break
            wr = sum(weights[i:])
            sl = rem * weights[i] / wr
            _search(q, d, D, rng, now + sl, consider)

    n, E = best["n"], best["E"]
    if not lib.is_valid(n, E, d, D):
        n, E = lib.haar_graph(d, range(d))
    return n, list(E)
