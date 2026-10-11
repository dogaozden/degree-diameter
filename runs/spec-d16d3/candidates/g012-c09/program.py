import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: incidence graph of PG(2, q), q the largest prime power with q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# From PG(2, q) incidence with spare capacity s = d - q - 1, pick a point set S
# such that every line holds <= s points of S and every point lies on <= s lines
# indexed by S. Add an A-vertex per point of S (joined to its q+1 lines) and a
# B-vertex per line of S (joined to its q+1 points). Diameter stays 3.
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S (all loads <= s), starting from S0."""
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
    """Return (n, edges) candidates from arc-extended PG(2, q) graphs with q + 1 <= d."""
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
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
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
# NEW: repair-based vertex insertion ("cover, saturate, then 2-switch repair").
#
# Growing a valid graph by one vertex v on side 1-c needs a neighbour set T on
# side c such that every vertex lies within distance D-1 of T. A greedy cover
# often misses a few vertices. Instead of giving up, we:
#   1. add v joined to a greedy partial cover T (|T| <= d),
#   2. saturate spare degree with new edges (this never increases distances),
#   3. run a short degree-preserving 2-switch annealing on the bad-pair count,
#   4. keep the result only if the diameter bound is met, else roll back.
# ----------------------------------------------------------------------------

def _reach_masks(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable counted)."""
    ball = _reach_masks(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _color_of(n, adj):
    """Two-colouring of a bipartite graph given by neighbour sets."""
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


def _cover_set(n, adj, color, c, d, D, rng, randomize):
    """Greedy partial cover of all vertices within D-1 by neighbours on side c (<= d of them)."""
    ball = _reach_masks(n, adj, D - 1)
    full = (1 << n) - 1
    cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
    covered = 0
    chosen = []
    while cands and len(chosen) < d and covered != full:
        gains = [(ball[s] & ~covered).bit_count() for s in cands]
        best_g = max(gains)
        if best_g <= 0:
            break
        if randomize and rng.random() < 0.5:
            opts = [i for i, g in enumerate(gains) if g >= best_g - 1 and g > 0]
            i = rng.choice(opts)
        else:
            i = gains.index(best_g)
        s = cands.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _saturate(n, adj, color, d, rng):
    """Join deficient opposite-side vertices with new edges (adding edges never hurts distances)."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(left)
    rng.shuffle(right)
    for a in left:
        for b in right:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)


def _switch(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Degrees are preserved."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _repair(n, adj, color, D, rng, deadline, steps):
    """Degree-preserving 2-switch annealing on the bad-pair count. Returns the final count."""
    L0 = [v for v in range(n) if color[v] == 0 and adj[v]]
    if len(L0) < 2:
        return _bad(n, adj, D)
    cur = _bad(n, adj, D)
    T0 = 0.7
    for _ in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(L0)
        c = rng.choice(L0)
        if a == c:
            continue
        b = rng.choice(list(adj[a]))
        e = rng.choice(list(adj[c]))
        if b == e or e in adj[a] or b in adj[c]:
            continue
        _switch(adj, a, b, c, e)
        new = _bad(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T0):
            cur = new
        else:
            _switch(adj, a, e, c, b)  # undo
    return cur


def _grow(n, edges, d, D, target, deadline, rng):
    """Repeatedly insert vertices with repair; returns the largest valid (n, edges) reached."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _color_of(n, adj)
    cur_n = n
    last = (n, list(edges))
    fails = 0
    while cur_n < target and time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        old_n = cur_n
        c = rng.randrange(2)
        T = _cover_set(cur_n, adj, color, c, d, D, rng, fails > 0)
        if not T:
            fails += 1
            continue
        v = cur_n
        adj.append(set())
        color.append(1 - c)
        for s in T:
            adj[s].add(v)
            adj[v].add(s)
        cur_n += 1
        _saturate(cur_n, adj, color, d, rng)
        bad = _bad(cur_n, adj, D)
        if bad:
            bad = _repair(cur_n, adj, color, D, rng, deadline, 150)
        if bad == 0:
            fails = 0
            last = (cur_n, [(x, y) for x in range(cur_n) for y in adj[x] if x < y])
        else:
            adj, color, cur_n = snap_adj, snap_color, old_n
            fails += 1
    return last


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            # Arc-extended graphs carry the spare degree that the repair growth uses.
            for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                            random.Random(seed * 7919 + d), best_n):
                consider(n_c, e_c)

    target = lib._moore_bound(d, D)
    if best_n < target and time.monotonic() < deadline:
        n_g, e_g = _grow(best_n, best_e, d, D, target, deadline, rng)
        consider(n_g, e_g)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
