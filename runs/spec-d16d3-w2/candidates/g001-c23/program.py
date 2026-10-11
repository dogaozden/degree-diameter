import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc-extended graphs (diameter 3).
#
# From PG(2, q) incidence with spare capacity s = d - q - 1 per vertex, pick a
# point set S with every line holding <= s points of S and every point on <= s
# lines of S. Add an A-vertex per point of S (joined to its q+1 lines) and a
# B-vertex per line of S (joined to its q+1 points). Diameter stays 3.
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
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


def _arc_extensions(d, deadline, rng, threshold):
    """Return (n, edges) candidates for prime powers q with q + 1 <= d."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40,
                                 now + 0.3 * share))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Twin saturation: a twin has the same neighbourhood as an existing vertex, so
# distances between old vertices are unchanged and diameter is preserved.
# ----------------------------------------------------------------------------

def _twin_saturate(n, edges, d, D, rng, deadline):
    """Repeatedly add twins of vertices whose neighbours all have spare degree."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        adj.append(list(adj[v]))
        for u in adj[t]:
            adj[u].append(t)
            edges.append((u, t))
    return n, edges


# ----------------------------------------------------------------------------
# NEW: insertion with annealed degree-preserving repair.
#
# Each step adds one vertex on a chosen side, joined to spare-degree vertices of
# the opposite side, then greedily saturates spare degree. The new graph is
# usually at diameter > D, so simulated annealing repairs it with two move types
# that keep every degree <= d and the graph bipartite:
#   - endpoint move: edge (x, y) becomes (x, z), z on y's side with spare degree;
#   - 2-switch: edges (x, y), (x2, y2) become (x, y2), (x2, y).
# Cost = number of ordered vertex pairs at distance > D (zero means valid).
# Only fully successful insertions are kept, so the output is always a valid
# graph with more vertices than the input.
# ----------------------------------------------------------------------------

def _sets_from(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _snapshot(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _cost_bits(n, adj, D):
    """Number of ordered pairs at distance > D (0 iff diameter <= D). Uses bitsets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _saturate(n, adj, color, d, rng):
    """Add edges between spare-degree opposite-side vertices (never increases distances)."""
    L = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    R = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in L for b in R if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _propose(n, adj, color, d, rng):
    """Apply a random degree-preserving move; return an undo callable, or None if no move was made."""
    x = rng.randrange(n)
    if not adj[x]:
        return None
    y = rng.choice(tuple(adj[x]))
    if rng.random() < 0.5:
        z = None
        for _ in range(30):
            c = rng.randrange(n)
            if color[c] == color[y] and c != y and c not in adj[x] and len(adj[c]) < d:
                z = c
                break
        if z is None:
            return None
        adj[x].discard(y)
        adj[y].discard(x)
        adj[x].add(z)
        adj[z].add(x)

        def undo_move():
            adj[x].discard(z)
            adj[z].discard(x)
            adj[x].add(y)
            adj[y].add(x)
        return undo_move

    x2 = rng.randrange(n)
    if x2 == x or color[x2] != color[x] or not adj[x2]:
        return None
    y2 = rng.choice(tuple(adj[x2]))
    if y2 == y or y2 in adj[x] or y in adj[x2]:
        return None
    adj[x].discard(y)
    adj[y].discard(x)
    adj[x2].discard(y2)
    adj[y2].discard(x2)
    adj[x].add(y2)
    adj[y2].add(x)
    adj[x2].add(y)
    adj[y].add(x2)

    def undo_switch():
        adj[x].discard(y2)
        adj[y2].discard(x)
        adj[x2].discard(y)
        adj[y].discard(x2)
        adj[x].add(y)
        adj[y].add(x)
        adj[x2].add(y2)
        adj[y2].add(x2)
    return undo_switch


def _insert_repair(n, edges, d, D, deadline, rng):
    """Insert vertices one at a time and repair diameter by annealing. Returns (n, edges) of the best valid graph."""
    best_n, best_e = n, list(edges)
    adj = _sets_from(n, edges)
    color = _bipartition(n, adj)
    side = 0
    fails = 0
    while time.monotonic() < deadline and fails < 3 and n < lib.moore_bound(d, D):
        cands = [v for v in range(n) if color[v] != side and len(adj[v]) < d]
        if not cands:
            side ^= 1
            cands = [v for v in range(n) if color[v] != side and len(adj[v]) < d]
            if not cands:
                break
        w = n
        n += 1
        adj.append(set())
        color.append(side)
        for u in rng.sample(cands, min(d, len(cands))):
            adj[w].add(u)
            adj[u].add(w)
        _saturate(n, adj, color, d, rng)
        cost = _cost_bits(n, adj, D)

        now = time.monotonic()
        span_end = min(deadline, now + max(1.0, 0.5 * (deadline - now)))
        t0 = now
        span = max(1e-3, span_end - t0)
        while cost > 0 and time.monotonic() < span_end:
            frac = (time.monotonic() - t0) / span
            T = 1.0 * (0.03 ** frac)
            undo = _propose(n, adj, color, d, rng)
            if undo is None:
                continue
            c2 = _cost_bits(n, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                undo()

        if cost == 0:
            best_n = n
            best_e = _snapshot(n, adj)
            side ^= 1
        else:
            fails += 1
            n = best_n
            adj = _sets_from(best_n, best_e)
            color = _bipartition(best_n, adj)
            side ^= 1
    return best_n, best_e


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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Arc-extended projective plane graphs (short budget: the conic gives the main value).
        arc_deadline = start + 0.12 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline,
                                        random.Random(seed * 7919 + d), best[0]):
            consider(n_c, e_c)
            n_t, e_t = _twin_saturate(n_c, e_c, d, D, random.Random(seed * 104729 + 17),
                                      min(deadline, time.monotonic() + 0.02 * time_limit))
            consider(n_t, e_t)

        # NEW: insertion with annealed repair, using the rest of the budget.
        if best[0] < lib.moore_bound(d, D) and time.monotonic() < deadline:
            n_r, e_r = _insert_repair(best[0], best[1], d, D, deadline, rng)
            consider(n_r, e_r)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
