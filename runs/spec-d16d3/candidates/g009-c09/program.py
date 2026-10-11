import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q).

    Points and lines are both indexed 0..m-1; point_lines[P] lists lines through P,
    line_points[L] lists points on L.
    """
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# Independent load-bounded sets (new: points and lines are chosen separately).
#
# A point set SA adds one new vertex x_P per P in SA, joined to the lines through P.
# A line set SB adds one new vertex y_M per M in SB, joined to the points on M.
# The constraints decouple: each line may carry at most `cap` SA points, and each
# point at most `cap` SB lines. Both sides are searched independently.
# ----------------------------------------------------------------------------

def _load_greedy(m, cap, targets, rng, trials, deadline):
    """Randomized greedy: pick elements e so that every target index is hit at most `cap` times.

    targets[e] lists the target indices element e loads. Returns the largest set found.
    """
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for e in order:
            t = targets[e]
            if all(load[x] < cap for x in t):
                S.append(e)
                for x in t:
                    load[x] += 1
        if len(S) > len(best):
            best = S
    return best


def _load_improve(m, cap, targets, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search on the load-bounded selection (see _load_greedy)."""
    load = [0] * m
    inS = [False] * m

    def add(e):
        inS[e] = True
        for x in targets[e]:
            load[x] += 1

    def rem(e):
        inS[e] = False
        for x in targets[e]:
            load[x] -= 1

    def fits(e):
        return all(load[x] < cap for x in targets[e])

    cur = []
    for e in S:
        add(e)
        cur.append(e)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        e = rng.randrange(m)
        if inS[e]:
            continue
        if fits(e):
            add(e)
            cur.append(e)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        r = cur[idx]
        rem(r)
        if fits(e):
            add(e)
            cur[idx] = e
        else:
            add(r)
    return best


def _indep_graph(m, edges, point_lines, line_points, SA, SB):
    """PG(2,q) incidence plus an x-vertex per point of SA and a y-vertex per line of SB."""
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    base_x = 2 * m
    for t, P in enumerate(SA):
        x = base_x + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_y = base_x + len(SA)
    for t, M in enumerate(SB):
        y = base_y + t
        for Q in line_points[M]:
            E.append((Q, y))
    return n, E


# ----------------------------------------------------------------------------
# Twin cloning (new helper): blow-up by vertex duplication with spare degree.
#
# A twin c of v has exactly the same neighbourhood as v. Distances between old
# vertices are unchanged, and twins are at distance 2, so the diameter is kept.
# Cloning v adds one to the degree of each neighbour, so it is allowed only when
# every neighbour has spare degree. The result stays bipartite (c has v's colour).
# ----------------------------------------------------------------------------

def _twin_augment(n, edges, d, deadline):
    """Repeatedly add a twin of a vertex whose neighbours all have spare degree."""
    E = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        found = -1
        for v in range(n):
            if not adj[v] or len(adj[v]) > d:
                continue
            if all(len(adj[u]) < d for u in adj[v]):
                found = v
                break
        if found < 0:
            break
        v = found
        c = n
        n += 1
        nbrs = list(adj[v])
        adj.append(nbrs)
        for u in nbrs:
            adj[u].append(c)
            E.append((u, c))
    return n, E


# ----------------------------------------------------------------------------
# Search drivers.
# ----------------------------------------------------------------------------

def _arc_search(d, q, deadline, rng, consider):
    """Independent load-bounded point/line sets on PG(2, q), each followed by twin augmentation."""
    s = d - q - 1
    if s < 1:
        return
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    if s >= 2:
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        n, e = _indep_graph(m, edges, point_lines, line_points, cs, cs)
        n, e = _twin_augment(n, e, d, deadline)
        consider(n, e)
    while time.monotonic() < deadline:
        SA = _load_greedy(m, s, point_lines, rng, 4, deadline)
        SA = _load_improve(m, s, point_lines, SA, rng, deadline, 1500)
        SB = _load_greedy(m, s, line_points, rng, 4, deadline)
        SB = _load_improve(m, s, line_points, SB, rng, deadline, 1500)
        n, e = _indep_graph(m, edges, point_lines, line_points, SA, SB)
        n, e = _twin_augment(n, e, d, deadline)
        consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*_twin_augment(pg[0], pg[1], d, deadline))
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(*_twin_augment(gq[0], gq[1], d, start + 0.5 * (deadline - start)))
            consider(gq[0], gq[1])

    if D >= 3:
        qs = [q for q in range(min(d - 2, 23), 1, -1) if lib.is_prime_power(q)][:3]
        if qs:
            t0 = time.monotonic()
            span = max(0.0, deadline - t0)
            if len(qs) == 1:
                weights = [1.0]
            else:
                weights = [0.6] + [0.4 / (len(qs) - 1)] * (len(qs) - 1)
            acc = 0.0
            for q, w in zip(qs, weights):
                acc += w
                sub_deadline = t0 + span * acc
                _arc_search(d, q, sub_deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
