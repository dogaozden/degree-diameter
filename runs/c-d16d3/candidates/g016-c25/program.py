import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Pick a point set S
# where each line holds <= s points of S and each point lies on <= s lines
# indexed by S. Add one new A-vertex per P in S (joined to the lines through P)
# and one new B-vertex per j in S (joined to the points on line j).
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    """Two-colouring by BFS (valid for a bipartite graph)."""
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


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    return lib.bad_pairs(n, [(u, v) for u in range(n) for v in adj[u] if u < v], D)


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# NEW: annealed repair search with undo log.
#
# Works on a valid bipartite graph with max degree d and diameter D. The state
# may become temporarily invalid. The objective is the number of vertex pairs
# at distance > D. Moves:
#   fill   : add a cross edge between two spare vertices (never hurts),
#   delete : remove an edge (creates spare capacity),
#   swap   : double-edge swap (a,b),(c,e) -> (a,e),(c,b), degrees preserved,
#   grow   : new vertex on one side, joined greedily to spare opposite-side
#            vertices that cover the R = D-1 balls.
# Moves are accepted by the Metropolis rule on the pair count. Any state with
# zero bad pairs is a valid graph, and the largest one is returned.
# ----------------------------------------------------------------------------

def _greedy_cover(N, balls, cand, d):
    """Greedy pick of up to d candidates maximising newly covered vertices."""
    covered = 0
    chosen = []
    pool = list(cand)
    while len(chosen) < d and pool:
        bg, bi = 0, -1
        for i, u in enumerate(pool):
            g = (balls[u] & ~covered).bit_count()
            if g > bg:
                bg, bi = g, i
        if bi < 0:
            break
        u = pool.pop(bi)
        chosen.append(u)
        covered |= balls[u]
    return chosen


def _repair_search(n0, edges0, d, D, rng, deadline):
    """Simulated annealing over bipartite graphs. Returns (n, edges) with n > n0 and valid, or None."""
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n0, adj)
    log = []

    def add_e(u, v):
        adj[u].add(v)
        adj[v].add(u)
        log.append((1, u, v))

    def del_e(u, v):
        adj[u].discard(v)
        adj[v].discard(u)
        log.append((0, u, v))

    def add_v(side):
        adj.append(set())
        color.append(side)
        log.append((2, side, 0))

    def undo():
        while log:
            op, u, v = log.pop()
            if op == 1:
                adj[u].discard(v)
                adj[v].discard(u)
            elif op == 0:
                adj[u].add(v)
                adj[v].add(u)
            else:
                adj.pop()
                color.pop()

    def fill():
        N = len(adj)
        spa = [u for u in range(N) if color[u] == 0 and len(adj[u]) < d]
        spb = [u for u in range(N) if color[u] == 1 and len(adj[u]) < d]
        if not spa or not spb:
            return False
        for _ in range(30):
            a = rng.choice(spa)
            b = rng.choice(spb)
            if b not in adj[a] and len(adj[a]) < d and len(adj[b]) < d:
                add_e(a, b)
                return True
        return False

    def step():
        N = len(adj)
        r = rng.random()
        if r < 0.10:
            return fill()
        if r < 0.20:
            a = rng.randrange(N)
            if not adj[a]:
                return False
            b = rng.choice(list(adj[a]))
            del_e(a, b)
            return True
        if r < 0.70:
            a = rng.randrange(N)
            if not adj[a]:
                return False
            b = rng.choice(list(adj[a]))
            same = [c for c in range(N) if color[c] == color[a] and c != a and adj[c]]
            if not same:
                return False
            c = rng.choice(same)
            e = rng.choice(list(adj[c]))
            if e == b or e in adj[a] or b in adj[c]:
                return False
            del_e(a, b)
            del_e(c, e)
            add_e(a, e)
            add_e(c, b)
            return True
        side = rng.randrange(2)
        cand = [u for u in range(N) if color[u] == 1 - side and len(adj[u]) < d]
        if not cand:
            return False
        rng.shuffle(cand)
        balls = _ball_masks(N, adj, D - 1)
        chosen = _greedy_cover(N, balls, cand, d)
        if not chosen:
            return False
        w = N
        add_v(side)
        for u in chosen:
            add_e(u, w)
        return True

    # Use every spare cross edge first.
    for _ in range(5000):
        if not fill():
            break

    cur = _bad_pairs(len(adj), adj, D)
    best_n, best_e = -1, None
    if cur == 0:
        best_n = len(adj)
        best_e = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
        best_n = -1  # only report graphs strictly larger than n0

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 3.0 * (1.0 - frac) + 0.3 * frac
        log.clear()
        if not step():
            continue
        N = len(adj)
        new = _bad_pairs(N, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur == 0 and N > max(best_n, n0):
                best_n = N
                best_e = [(u, v) for u in range(N) for v in adj[u] if u < v]
        else:
            undo()
    if best_e is not None and best_n > n0:
        return best_n, best_e
    return None


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

    # Arc-extended projective plane graphs (diameter 3), then greedy insertion.
    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.25 * time_limit)
            consider(n2, e2)

    # New stage: annealed repair/growth from the best valid graph so far.
    if D >= 2 and time.monotonic() < start + 0.80 * time_limit:
        try:
            found = _repair_search(best_n, best[1], d, D, rng, start + 0.85 * time_limit)
            if found is not None:
                consider(found[0], found[1])
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
