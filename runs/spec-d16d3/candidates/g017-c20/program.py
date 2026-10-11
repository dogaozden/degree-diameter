import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with spare s = d - q - 1 per vertex, pick a point set S with every line
# holding <= s points of S and every point on <= s lines indexed by S. Add an
# A-vertex per P in S (joined to the q+1 lines through P) and a B-vertex per
# j in S (joined to the q+1 points on line j). For d=16, q=13 a conic gives
# 2(q^2+q+1) + 2(q+1) = 394 vertices.
#
# New helper: covering-based insertion with random rewiring.
#   A new vertex x on side c is valid iff every side-c vertex is within
#   distance 2 of x (a common neighbour) and every opposite-side vertex is
#   within distance 3. The first condition is a set-cover problem over
#   vertices with spare degree, solved greedily. Candidates are checked with
#   lib.is_valid. A random walk over valid graphs with spare degree (edge
#   rewiring) explores more states between insertion attempts.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, incidence_edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, inc = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in inc:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, inc, point_lines, line_points, index


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
    """Randomized greedy S with all loads <= s; returns the largest found."""
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


def _arc_graph(m, inc, point_lines, line_points, S):
    """Old PG incidence plus A (point side) and B (line side) vertices for each element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(inc)
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


def _best_arc(d, deadline, rng):
    """Return (n, edges, side) for the largest arc extension over prime powers q with q+1 <= d."""
    best = None
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        if time.monotonic() > deadline:
            break
        F = lib.GF(q)
        m, inc, pl, lp, index = _pg(q)
        cands = [[]]
        if s >= 2:
            cands.append(_conic_set(q, index, F))
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 30, deadline))
        ok = [S for S in cands if _loads_ok(S, s, m, pl, lp)]
        S = max(ok, key=len)
        n, E, side = _arc_graph(m, inc, pl, lp, S)
        if best is None or n > best[0]:
            best = (n, E, side)
    return best


# ----------------------------------------------------------------------------
# Covering insertion and rewiring search.
# ----------------------------------------------------------------------------

def _edge_list(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _cover_choice(n, adj, side, c, d, rng):
    """Greedy set cover: neighbours (side != c, spare degree) covering all side-c vertices within 2."""
    targets = [v for v in range(n) if side[v] == c]
    if not targets:
        return None
    idx = {v: i for i, v in enumerate(targets)}
    cands = [u for u in range(n) if side[u] != c and len(adj[u]) < d]
    rng.shuffle(cands)
    cov = {}
    for u in cands:
        mask = 0
        for w in adj[u]:
            i = idx.get(w)
            if i is not None:
                mask |= 1 << i
        if mask:
            cov[u] = mask
    unc = (1 << len(targets)) - 1
    chosen = []
    while unc:
        if len(chosen) >= d or not cov:
            return None
        u_best = max(cov, key=lambda u: bin(cov[u] & unc).count("1"))
        if (cov[u_best] & unc) == 0:
            return None
        chosen.append(u_best)
        unc &= ~cov[u_best]
        del cov[u_best]
    return chosen


def _repair(n, E, side, d, D, deadline, rng):
    """Random walk over valid graphs, trying insertions of new vertices. Returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side)
    while time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        if rng.random() < 0.5:
            # Insertion attempt, after freeing a few random edges.
            trial = [set(s) for s in adj]
            for _ in range(rng.choice((0, 1, 2, 3))):
                u = rng.randrange(n)
                if trial[u]:
                    v = rng.choice(sorted(trial[u]))
                    trial[u].discard(v)
                    trial[v].discard(u)
            c = rng.randrange(2)
            chosen = _cover_choice(n, trial, side, c, d, rng)
            if chosen is None:
                continue
            trial.append(set(chosen))
            for u in chosen:
                trial[u].add(n)
            E2 = _edge_list(trial)
            if lib.is_valid(n + 1, E2, d, D):
                adj = trial
                n += 1
                side.append(c)
        else:
            # Rewire: move one endpoint of an edge to a spare vertex on the same side.
            u = rng.randrange(n)
            if not adj[u]:
                continue
            v = rng.choice(sorted(adj[u]))
            cands = [w for w in spare if side[w] == side[v] and w != v and w not in adj[u]]
            if not cands:
                continue
            w = rng.choice(cands)
            trial = [set(s) for s in adj]
            trial[u].discard(v)
            trial[v].discard(u)
            trial[u].add(w)
            trial[w].add(u)
            E2 = _edge_list(trial)
            if lib.is_valid(n, E2, d, D):
                adj = trial
    return n, _edge_list(adj)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D (Moore-optimal).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for all D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best_n, best_E = fallback

    arc = _best_arc(d, start + 0.3 * budget, rng)
    if arc is not None and arc[0] > best_n and lib.is_valid(arc[0], arc[1], d, D):
        best_n, best_E = arc[0], arc[1]
        res_n, res_E = _repair(arc[0], arc[1], arc[2], d, D, deadline, rng)
        if res_n > best_n and lib.is_valid(res_n, res_E, d, D):
            best_n, best_E = res_n, res_E

    if not lib.is_valid(best_n, best_E, d, D):
        return fallback
    return best_n, best_E
