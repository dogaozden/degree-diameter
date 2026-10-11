import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: PG(2, q) incidence plus an arc-extension (diameter 3).
#
# Each point of an arc S gets an A-vertex joined to the q+1 lines through it,
# and each line of S gets a B-vertex joined to the q+1 points on it. Diameter
# stays 3 for any S. Degree limits require every line to contain <= s points
# of S and every point to lie on <= s lines of S, where s = d - q - 1.
# ----------------------------------------------------------------------------

def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Return (n, edges, color) for PG(2,q) incidence plus A/B vertices for the arc S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    color = [0] * m + [1] * m + [0] * k + [1] * k
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, L0 in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[L0]:
            E.append((Q, b))
    return n, E, color


def _pg_arc_base(d, rng, deadline):
    """Best arc-extended PG(2,q) over prime powers q with q + 1 <= d. Returns (n, edges, color) or None."""
    best = None
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        m2, edges = lib.projective_plane_incidence(q)
        m = m2 // 2
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 25, deadline))
        if s >= 2:
            F = lib.GF(q)
            cands.append(_conic_set(q, index, F))
        valid = [S for S in cands if _loads_ok(S, s, m, point_lines, line_points)]
        S = max(valid, key=len)
        n_c, E_c, col_c = _arc_graph(m, edges, point_lines, line_points, S)
        if best is None or n_c > best[0]:
            best = (n_c, E_c, col_c)
    return best


# ----------------------------------------------------------------------------
# Generic vertex growth with verification.
#
# A new vertex x of colour c is valid (for diameter D) iff its neighbours,
# all of the opposite colour with spare degree, have radius-(D-1) balls that
# together cover every existing vertex. Adding edges and vertices never
# breaks existing distances, so growth is sound; the result is still checked
# with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _adj_from(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, noisy):
    """Greedy (optionally noisy) cover of `full` by at most d candidate balls; None on failure."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        scored = []
        for s in pool:
            g = (ball[s] & ~covered).bit_count()
            if g:
                scored.append((g, rng.random(), s))
        if not scored:
            break
        scored.sort(reverse=True)
        if noisy and len(scored) > 1 and rng.random() < 0.3:
            pick = scored[rng.randrange(min(3, len(scored)))]
        else:
            pick = scored[0]
        s = pick[2]
        chosen.append(s)
        covered |= ball[s]
        pool.remove(s)
    return chosen if covered == full else None


def _try_add(n, adj, color, d, balls, rng, tries):
    """Try to find (colour, neighbours) for a new vertex that keeps diameter. None on failure."""
    full = (1 << n) - 1
    order = [0, 1]
    rng.shuffle(order)
    for cc in order:
        cands = [s for s in range(n) if color[s] == 1 - cc and len(adj[s]) < d]
        if not cands:
            continue
        for t in range(tries):
            chosen = _greedy_cover(cands, balls, full, d, rng, t > 0)
            if chosen:
                return cc, chosen
    return None


def _remove_extra(adj, color, base_n, rng):
    """Delete a random extra vertex (index >= base_n) by relabelling the last vertex into its slot."""
    n = len(adj)
    if n <= base_n:
        return
    v = rng.randrange(base_n, n)
    last = n - 1
    for w in adj[v]:
        adj[w].remove(v)
    if v != last:
        for w in adj[last]:
            lst = adj[w]
            lst[lst.index(last)] = v
        adj[v] = adj[last]
        color[v] = color[last]
    adj.pop()
    color.pop()


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = min(0.8 * float(time_limit), 45.0)
    deadline = t0 + budget
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is Moore-optimal for D = 2; it is the safe fallback.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    if D == 2:
        return fb_n, fb_E

    base = _pg_arc_base(d, rng, t0 + 0.1 * budget)
    if base is None:
        return fb_n, fb_E
    n0, E0, col0 = base
    if not lib.is_valid(n0, E0, d, D):
        return fb_n, fb_E

    best_n, best_E = n0, list(E0)
    base_n = n0
    adj = _adj_from(n0, E0)
    color = list(col0)
    best_adj = [list(a) for a in adj]
    best_color = list(color)

    balls = None
    fails = 0
    while time.monotonic() < deadline:
        n = len(adj)
        if balls is None:
            balls = _balls(n, adj, D - 1)
        res = _try_add(n, adj, color, d, balls, rng, 3)
        if res is not None:
            cc, chosen = res
            adj.append(list(chosen))
            color.append(cc)
            for s in chosen:
                adj[s].append(n)
            balls = None
            fails = 0
            if n + 1 > best_n:
                E = _edges_of(adj)
                if lib.is_valid(n + 1, E, d, D):
                    best_n, best_E = n + 1, E
                    best_adj = [list(a) for a in adj]
                    best_color = list(color)
            continue

        # Stuck: return to the best verified graph and perturb it.
        fails += 1
        if fails >= 60:
            fails = 0
            adj = [list(a) for a in best_adj]
            color = list(best_color)
            if len(adj) > base_n and rng.random() < 0.7:
                _remove_extra(adj, color, base_n, rng)
            balls = None

    if not lib.is_valid(best_n, best_E, d, D):
        return fb_n, fb_E
    return best_n, best_E
