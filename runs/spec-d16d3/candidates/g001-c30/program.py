import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Conic (plus nucleus for even q) as a point-index set."""
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
# Pair augmentation with edge-level repair (a different construction family).
#
# Each step adds one A-vertex a and one B-vertex b, joined to each other and to
# as many deficient opposite-side vertices as their spare degree allows.
# The neighbour sets are chosen by hill-climbing on the number of bad pairs.
# A step is kept only if the result has diameter <= D. Adding edges never
# increases distances, so full-size neighbour sets are always the best choice.
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


def _with_pair(E, a, b, Na, Nb):
    """Edge list with new vertices a (A-side) and b (B-side) added."""
    return E + [(x, a) for x in Na] + [(y, b) for y in Nb] + [(a, b)]


def _augment(n, E, d, D, deadline, rng, iters=150, max_fail=6):
    """Repeatedly add a vertex pair whose neighbourhoods keep diameter <= D."""
    E = list(E)
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    fails = 0

    while time.monotonic() < deadline and fails < max_fail:
        A_def = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        B_def = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        ka = min(d - 1, len(B_def))
        kb = min(d - 1, len(A_def))
        if ka < 1 or kb < 1:
            break

        a, b = n, n + 1
        Na = rng.sample(B_def, ka)
        Nb = rng.sample(A_def, kb)
        cost = lib.bad_pairs(n + 2, _with_pair(E, a, b, Na, Nb), D)

        for _ in range(iters):
            if cost == 0 or time.monotonic() >= deadline:
                break
            can_a = len(B_def) > ka
            can_b = len(A_def) > kb
            if not (can_a or can_b):
                break
            if can_a and (not can_b or rng.random() < 0.5):
                i = rng.randrange(ka)
                x = rng.choice(B_def)
                if x in Na:
                    continue
                Na2 = Na[:]
                Na2[i] = x
                Nb2 = Nb
            else:
                i = rng.randrange(kb)
                y = rng.choice(A_def)
                if y in Nb:
                    continue
                Nb2 = Nb[:]
                Nb2[i] = y
                Na2 = Na
            c2 = lib.bad_pairs(n + 2, _with_pair(E, a, b, Na2, Nb2), D)
            if c2 <= cost:
                Na, Nb, cost = Na2, Nb2, c2

        if cost == 0:
            E = _with_pair(E, a, b, Na, Nb)
            deg.extend([0, 0])
            color.extend([0, 1])
            for x in Na:
                deg[x] += 1
            for y in Nb:
                deg[y] += 1
            deg[a] = len(Na) + 1
            deg[b] = len(Nb) + 1
            n += 2
            fails = 0
        else:
            fails += 1

    return n, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
        # Edge-level augmentation starting from the best graph found so far.
        n2, e2 = _augment(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
