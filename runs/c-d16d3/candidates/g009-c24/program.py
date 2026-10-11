import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Each old vertex has degree q+1, so with d >= q+1 it has spare s = d-q-1.
# Pick a point set S (an arc, or a random greedy set) with every line holding
# at most s points of S and every point lying on at most s lines indexed by S.
# For each P in S add a new A-vertex joined to the q+1 lines through P; for each
# j in S add a new B-vertex joined to the q+1 points on line j. Diameter stays 3.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
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


def _arc_graph(m, edges, point_lines, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # line j has the same vector as point j
        b = 2 * m + k + t
        for Q in _LP[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


_LP = None


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q+1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg(q)
        _LP = line_points
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S))
    return out


# ----------------------------------------------------------------------------
# New helper: greedy set-cover vertex insertion.
#
# A new vertex x joined to a set N of existing vertices (all on the opposite
# side of x) keeps diameter <= D exactly when the radius-(D-1) balls of the
# vertices in N together cover every old vertex: then every old vertex is
# within distance 1 + (D-1) of x, and old-old distances can only shrink.
# Bipartiteness is kept by putting x on the side opposite to N. We repeatedly
# pick a side, then choose N greedily (max new coverage, random ties) among
# vertices with spare degree. Each accepted insertion adds one vertex.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph given by adjacency sets."""
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


def _radius_masks(n, adj, k):
    """Bitmask of all vertices within distance k of each vertex."""
    r = [1 << v for v in range(n)]
    for _ in range(k):
        nr = []
        for v in range(n):
            x = r[v]
            for u in adj[v]:
                x |= r[u]
            nr.append(x)
        r = nr
    return r


def _augment(n, adj, color, d, D, rng, deadline, max_misses=300):
    """Insert new vertices by greedy set cover; adj and color are extended in place. Returns new n."""
    k = D - 1
    misses = 0
    while misses < max_misses and time.monotonic() < deadline:
        balls = _radius_masks(n, adj, k)
        full = (1 << n) - 1
        t = rng.randrange(2)
        cands = [u for u in range(n) if color[u] == 1 - t and len(adj[u]) < d]
        rng.shuffle(cands)
        covered = 0
        picked = []
        pool = cands
        while covered != full and len(picked) < d and pool:
            best_i, best_g = -1, 0
            for i, u in enumerate(pool):
                g = (balls[u] & ~covered).bit_count()
                if g > best_g:
                    best_g, best_i = g, i
            if best_i < 0:
                break
            u = pool.pop(best_i)
            picked.append(u)
            covered |= balls[u]
        if covered == full and picked:
            x = n
            n += 1
            adj.append(set())
            color.append(t)
            for u in picked:
                adj[u].add(x)
                adj[x].add(u)
            misses = 0
        else:
            misses += 1
    return n


def _run_augment(n0, e0, d, D, rng, deadline):
    """Run the insertion search from a starting graph; return (n, edges)."""
    adj = [set() for _ in range(n0)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n0, adj)
    n = _augment(n0, adj, color, d, D, rng, deadline)
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is always a valid fallback for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    starts = [fallback] + _arc_candidates(d, deadline, rng)
    starts = [s for s in starts if lib.is_valid(s[0], s[1], d, D)]
    starts.sort(key=lambda t: -t[0])
    best_n, best_e = starts[0]

    top = starts[:3]
    for i, (n0, e0) in enumerate(top):
        now = time.monotonic()
        if now >= deadline:
            break
        sub = now + (deadline - now) / (len(top) - i)
        n1, e1 = _run_augment(n0, e0, d, D, rng, sub)
        if n1 > best_n and lib.is_valid(n1, e1, d, D):
            best_n, best_e = n1, e1

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
