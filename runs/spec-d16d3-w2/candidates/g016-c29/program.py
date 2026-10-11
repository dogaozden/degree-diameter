import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S with
# every line holding <= s points of S and every point lying on <= s lines of S.
# For each P in S add an A-vertex joined to the q+1 lines through P; for each j in
# S add a B-vertex joined to the q+1 points on line j.
# ----------------------------------------------------------------------------

def _pg_data(q):
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S, point_lines, line_points):
    """Extended graph with a 2-colouring: points and A-vertices side 0, lines and B-vertices side 1."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_extensions(d, deadline, rng):
    """Return candidates (n, edges, side) for each prime power q with q + 1 <= d, largest first."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, S, pl, lp))
    out.sort(key=lambda t: -t[0])
    return out


# ----------------------------------------------------------------------------
# NEW: cover-based vertex insertion and exact diameter-3 local search.
#
# Key fact: in a graph of diameter <= 3, a new vertex x adjacent to a set N
# keeps diameter <= 3 iff the 2-balls of the vertices of N cover every vertex:
# dist(x, v) = 1 + min_{u in N} dist(u, v), so dist(x, v) <= 3 iff some u in N
# is within distance 2 of v. Old pairs cannot get farther apart by adding x.
# Bipartiteness holds if N lies entirely on one side and x on the other.
# So insertion becomes a set-cover problem over spare-degree vertices.
#
# The search repeatedly removes a few vertices, greedily refills with cover
# insertions, and keeps the result only if the graph is still of diameter 3.
# ----------------------------------------------------------------------------

def _masks(adj, alive):
    """Return (b2, full): b2[u] is a bitmask of all vertices within distance 2 of u; full is the alive mask."""
    n = len(adj)
    b1 = [0] * n
    full = 0
    for v in range(n):
        if alive[v]:
            full |= 1 << v
            m = 1 << v
            for w in adj[v]:
                m |= 1 << w
            b1[v] = m
    b2 = [0] * n
    for u in range(n):
        if alive[u]:
            m = b1[u]
            for w in adj[u]:
                m |= b1[w]
            b2[u] = m
    return b2, full


def _greedy_cover(pool, b2, full, d, rng):
    """Randomized greedy: pick up to d vertices from pool whose 2-balls cover full. Return (N, covered)."""
    covered = 0
    N = []
    pool = list(pool)
    while covered != full and len(N) < d and pool:
        best_g = 0
        best = []
        for u in pool:
            g = (b2[u] & ~covered).bit_count()
            if g > best_g:
                best_g = g
                best = [u]
            elif g == best_g and g > 0:
                best.append(u)
        if best_g == 0:
            break
        u = rng.choice(best)
        N.append(u)
        covered |= b2[u]
        pool.remove(u)
    return N, covered


def _attach(adj, side, alive, N, sx):
    """Add a new vertex on side sx adjacent to N (reusing a dead slot if one exists)."""
    x = next((v for v in range(len(adj)) if not alive[v]), None)
    if x is None:
        x = len(adj)
        adj.append(set())
        side.append(sx)
        alive.append(True)
    else:
        side[x] = sx
        alive[x] = True
    adj[x] = set(N)
    for u in N:
        adj[u].add(x)


def _try_insert(adj, side, alive, d, rng, b2, full):
    """Try to insert one vertex; return True on success."""
    n = len(adj)
    for _ in range(2):
        sides = [0, 1]
        rng.shuffle(sides)
        for s in sides:
            pool = [u for u in range(n) if alive[u] and side[u] == s and len(adj[u]) < d]
            if not pool:
                continue
            N, covered = _greedy_cover(pool, b2, full, d, rng)
            if N and covered == full:
                _attach(adj, side, alive, N, 1 - s)
                return True
    return False


def _fill(adj, side, alive, d, rng, max_fail=2):
    """Greedily insert vertices until max_fail consecutive attempts fail."""
    b2, full = _masks(adj, alive)
    fails = 0
    while fails < max_fail:
        if _try_insert(adj, side, alive, d, rng, b2, full):
            b2, full = _masks(adj, alive)
            fails = 0
        else:
            fails += 1


def _remove(adj, alive, v):
    """Remove v; cascade-remove neighbours left isolated."""
    nbrs = adj[v]
    alive[v] = False
    adj[v] = set()
    for u in nbrs:
        adj[u].discard(v)
    for u in nbrs:
        if alive[u] and not adj[u]:
            _remove(adj, alive, u)


def _diam_ok(adj, alive):
    """True iff all alive vertices are pairwise within distance 3 (connected, diameter <= 3)."""
    b2, full = _masks(adj, alive)
    for v in range(len(adj)):
        if alive[v]:
            r = b2[v]
            for u in adj[v]:
                r |= b2[u]
            if r != full:
                return False
    return True


def _has_spare(adj, alive, d):
    return any(alive[v] and len(adj[v]) < d for v in range(len(adj)))


def _snap(adj, side, alive):
    return ([set(s) for s in adj], list(side), list(alive))


def _restore(adj, side, alive, st):
    sa, ss, al = st
    adj[:] = [set(s) for s in sa]
    side[:] = ss
    alive[:] = al


def _extract(adj, alive):
    E = [(u, v) for u in range(len(adj)) if alive[u] for v in adj[u] if u < v]
    return lib.relabel(E)


def _search(adj, side, alive, d, D, deadline, rng):
    """Remove-and-refill local search keeping diameter <= 3. Returns (n, edges) or None."""
    if not _diam_ok(adj, alive):
        return None
    _fill(adj, side, alive, d, rng)
    cur = sum(alive)
    mb = lib.moore_bound(d, D)
    best_cnt, best_state = cur, _snap(adj, side, alive)
    while time.monotonic() < deadline and best_cnt < mb and _has_spare(adj, alive, d):
        snap = _snap(adj, side, alive)
        ids = [v for v in range(len(adj)) if alive[v]]
        k = 1 if rng.random() < 0.6 else 2
        for v in rng.sample(ids, min(k, len(ids))):
            if alive[v]:
                _remove(adj, alive, v)
        _fill(adj, side, alive, d, rng)
        new = sum(alive)
        if _diam_ok(adj, alive) and (new >= cur or rng.random() < 0.02):
            cur = new
            if cur > best_cnt:
                best_cnt, best_state = cur, _snap(adj, side, alive)
        else:
            _restore(adj, side, alive, snap)
    return _extract(best_state[0], best_state[2])


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    deadline = start + 0.8 * time_limit

    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, rng)
        for n_c, e_c, _side in cands:
            consider(n_c, e_c)

        if D == 3 and cands:
            n_c, e_c, side = cands[0]
            adj = [set() for _ in range(n_c)]
            alive = [True] * n_c
            for u, v in e_c:
                adj[u].add(v)
                adj[v].add(u)
            res = _search(adj, list(side), alive, d, D, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
