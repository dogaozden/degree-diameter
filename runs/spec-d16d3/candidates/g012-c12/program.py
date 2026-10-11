import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane and generalized-quadrangle bases.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# From PG(2, q), spare capacity s = d - q - 1 per vertex. Pick point set S and
# line set T with every line holding <= s points of S and every point on <= s
# lines of T. Add an A-vertex per point of S and a B-vertex per line of T.
# ----------------------------------------------------------------------------

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


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Shared graph-state helpers (adjacency as sets, colours for bipartition).
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


def _state(n, edges):
    """Return (nbrs, color) for a bipartite graph given as (n, edges)."""
    nbrs = [set() for _ in range(n)]
    for u, v in edges:
        nbrs[u].add(v)
        nbrs[v].add(u)
    color = _bipartition(n, [list(s) for s in nbrs])
    return nbrs, color


def _edges_of(nbrs):
    """Edge list of a state given by neighbour sets."""
    return [(u, v) for u in range(len(nbrs)) for v in nbrs[u] if u < v]


def _ball2(nbrs):
    """ball2[v]: bitmask of all vertices within distance 2 of v."""
    n = len(nbrs)
    r1 = [0] * n
    for v in range(n):
        m = 1 << v
        for u in nbrs[v]:
            m |= 1 << u
        r1[v] = m
    r2 = [0] * n
    for v in range(n):
        m = r1[v]
        for u in nbrs[v]:
            m |= r1[u]
        r2[v] = m
    return r2


def _diam3_ok(nbrs):
    """True if every pair of vertices is within distance 3 (graph connected, diameter <= 3)."""
    n = len(nbrs)
    full = (1 << n) - 1
    r2 = _ball2(nbrs)
    for x in range(n):
        m = r2[x]
        for u in nbrs[x]:
            m |= r2[u]
        if m != full:
            return False
    return True


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


# ----------------------------------------------------------------------------
# NEW HELPER 1: cover insertion.
# A new vertex of colour c is joined to a set C of opposite-colour vertices with
# spare degree. Its distance-3 reach is the union of radius-2 balls of C, so C
# is valid iff those balls cover the whole graph. Adding a vertex never breaks
# existing distances, so the diameter bound is preserved.
# ----------------------------------------------------------------------------

def _insert_one(nbrs, color, d, rng, tries):
    """Try to append one vertex whose neighbourhood covers everything within distance 2. True on success."""
    n = len(nbrs)
    r2 = _ball2(nbrs)
    full = (1 << n) - 1
    cs = [0, 1]
    rng.shuffle(cs)
    for c in cs:
        cands = [s for s in range(n) if color[s] == 1 - c and len(nbrs[s]) < d]
        if not cands:
            continue
        for t in range(tries):
            chosen = _greedy_cover(cands, r2, full, d, rng, t > 0)
            if chosen:
                v = n
                nbrs.append(set(chosen))
                color.append(c)
                for s in chosen:
                    nbrs[s].add(v)
                return True
    return False


def _grow_insert(n, edges, d, rng, rounds=60):
    """Repeatedly insert cover-vertices until none fits."""
    nbrs, color = _state(n, edges)
    for _ in range(rounds):
        if not _insert_one(nbrs, color, d, rng, 8):
            break
    return len(nbrs), _edges_of(nbrs)


# ----------------------------------------------------------------------------
# NEW HELPER 2: ruin-and-recreate local search.
# Remove a random vertex (swap-with-last compaction), then re-insert up to three
# cover-vertices. Accept if at least one vertex is re-inserted and diameter 3
# still holds; otherwise revert. A net gain is recorded as the best graph.
# ----------------------------------------------------------------------------

def _remove(nbrs, color, v):
    """Delete vertex v, moving the last vertex into its slot to keep labels compact."""
    for u in nbrs[v]:
        nbrs[u].discard(v)
    last = len(nbrs) - 1
    if v != last:
        for u in nbrs[last]:
            nbrs[u].discard(last)
            nbrs[u].add(v)
        nbrs[v] = nbrs[last]
        color[v] = color[last]
    nbrs.pop()
    color.pop()


def _ruin_recreate(n, edges, d, deadline, rng, max_moves):
    """Local search over diameter-3 graphs; returns the largest (n, edges) seen."""
    nbrs, color = _state(n, edges)
    best = (n, list(edges))
    moves = 0
    while moves < max_moves and time.monotonic() < deadline:
        moves += 1
        snap_n = [set(s) for s in nbrs]
        snap_c = color[:]
        v = rng.randrange(len(nbrs))
        _remove(nbrs, color, v)
        added = 0
        for _ in range(3):
            if not _insert_one(nbrs, color, d, rng, 6):
                break
            added += 1
        if added == 0 or not _diam3_ok(nbrs):
            nbrs, color = snap_n, snap_c
            continue
        if len(nbrs) > best[0]:
            best = (len(nbrs), _edges_of(nbrs))
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow_insert(pg[0], pg[1], d, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D == 3:
        # Spend the remaining budget on ruin-and-recreate from the best graph so far.
        n_r, e_r = _ruin_recreate(best[0], list(best[1]), d, deadline, rng, 3000)
        consider(n_r, e_r)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
