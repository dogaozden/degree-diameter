import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: arc-extended projective plane incidence graphs (diameter 3).
#
# PG(2, q) incidence graph plus, for each point P of an arc S, a new "A" vertex
# joined to the q+1 lines through P, and for each line j of S a new "B" vertex
# joined to the q+1 points on j. Spare degree of old vertices limits the arc.
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A vertex per point of S and a new B vertex per line of S."""
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


def _arc_candidates(d, deadline, rng):
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
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
        S = max(cands, key=len) if cands else []
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bold attempt for D = 3: grow the base graph by adding one A and one B vertex
# at a time, then repair with simulated annealing over edge moves (add, remove,
# and degree-preserving 2-switches). The cost is the number of vertex pairs at
# distance > 3. Bipartiteness is kept because edges only join opposite colours.
# Any failure returns the last snapshot that reached cost 0.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Proper 2-colouring of a bipartite graph (BFS, one component at a time)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] < 0:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, adj):
    """Number of unordered pairs at distance > 3 (bitset ball expansion, 3 rounds)."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n, adj, col, d, deadline, rng):
    """Anneal edges until no pair is farther than 3 apart. Returns True on success."""
    side = [[v for v in range(n) if col[v] == 0], [v for v in range(n) if col[v] == 1]]
    cur = _bad(n, adj)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = max(0.02, 1.2 * (1.0 - (now - t0) / span))
        r = rng.random()
        if r < 0.35:
            a = rng.choice(side[0])
            b = rng.choice(side[1])
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            adj[a].add(b)
            adj[b].add(a)
            c2 = _bad(n, adj)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        elif r < 0.5:
            a = rng.choice(side[0])
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            adj[a].discard(b)
            adj[b].discard(a)
            c2 = _bad(n, adj)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[a].add(b)
                adj[b].add(a)
        else:
            a1 = rng.choice(side[0])
            a2 = rng.choice(side[0])
            if a1 == a2 or not adj[a1] or not adj[a2]:
                continue
            b1 = rng.choice(tuple(adj[a1]))
            b2 = rng.choice(tuple(adj[a2]))
            if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            adj[a1].discard(b1); adj[b1].discard(a1)
            adj[a2].discard(b2); adj[b2].discard(a2)
            adj[a1].add(b2); adj[b2].add(a1)
            adj[a2].add(b1); adj[b1].add(a2)
            c2 = _bad(n, adj)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[a1].discard(b2); adj[b2].discard(a1)
                adj[a2].discard(b1); adj[b1].discard(a2)
                adj[a1].add(b1); adj[b1].add(a1)
                adj[a2].add(b2); adj[b2].add(a2)
    return True


def _repair_grow(base, d, deadline, rng):
    """Grow a valid D=3 graph by annealing; return the largest valid snapshot found."""
    n, E = base
    col = _two_color(n, E)
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    snap = (n, list(E))
    while time.monotonic() < deadline:
        adj.append(set())
        adj.append(set())
        col.append(0)
        col.append(1)
        n += 2
        if not _anneal(n, adj, col, d, deadline, rng):
            break
        snap = (n, [(u, v) for u in range(n) for v in adj[u] if u < v])
    return snap


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.75 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break

    if D == 3 and best[0] < lib._moore_bound(d, 3) and time.monotonic() < deadline:
        grown = _repair_grow(best, d, deadline, rng)
        if grown[0] > best[0] and lib.is_valid(grown[0], grown[1], d, D):
            best = grown

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
