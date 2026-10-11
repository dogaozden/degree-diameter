"""Arc-extended PG(2,q) baseline plus a bold annealing search for one extra vertex at a time.

Baseline (proven valid): incidence graph of PG(2,q) with q the largest usable prime power,
extended by A-vertices (pencils through a point set SA) and B-vertices (dual pencils on a
line set SB), with loads bounded by s = d - q - 1. For d=16 this is q=13 and reaches 394.

Bold step: starting from the best valid baseline, add one vertex at a time and anneal edge
rewires (keeping bipartiteness and max degree d) to drive the number of pairs at distance
> D to zero. Every success is checked with lib.is_valid, and the search stops at the
deadline. The fallback K_{d,d} is returned if nothing valid is found.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q).

    Points are 0..m-1 and lines are m..2m-1; line j has the same coordinate vector as point j.
    """
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


def _set_ok(S, s, incident, m):
    """True if every target is loaded at most s times by the elements of S."""
    load = [0] * m
    for i in S:
        for t in incident[i]:
            load[t] += 1
    return all(x <= s for x in load)


def _greedy_set(m, s, incident, rng, trials, deadline):
    """Randomised greedy choice of elements whose target loads stay <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for i in order:
            tg = incident[i]
            if all(load[t] < s for t in tg):
                S.append(i)
                for t in tg:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus when q is even) as a set of point indices."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old incidence graph plus an A-vertex per SA point and a B-vertex per SB line."""
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    x = 2 * m
    for P in SA:
        for L in point_lines[P]:
            E.append((x, m + L))
        x += 1
    for j in SB:
        for Q in line_points[j]:
            E.append((Q, x))
        x += 1
    return n, E


def _arc_candidates(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        SA, SB = [], []
        if s >= 1:
            SA = _greedy_set(m, s, point_lines, rng, 30, deadline)
            SB = _greedy_set(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if len(cs) > len(SA) and _set_ok(cs, s, point_lines, m):
                SA = cs
            if len(cs) > len(SB) and _set_ok(cs, s, line_points, m):
                SB = cs
        n, E = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# Bold search: grow the baseline one vertex at a time by annealing edge rewires.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of a bipartite graph."""
    nbr = [[] for _ in range(n)]
    for u, v in edges:
        nbr[u].append(v)
        nbr[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in nbr[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _classes(colors):
    cls = [[], []]
    for v, c in enumerate(colors):
        cls[c].append(v)
    return cls


def _search(n0, edges0, d, D, rng, deadline, state):
    """Add vertices one at a time, annealing edge rewires until the diameter bound holds.

    state['best'] = (n, edges) holds the largest valid graph found so far.
    """
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    colors = _two_color(n0, edges0)

    while time.monotonic() < deadline:
        x = len(adj)
        n = x + 1
        c = rng.randrange(2)
        adj.append(set())
        colors.append(c)
        cls = _classes(colors)

        # Attach the new vertex to up to d opposite-side vertices with spare degree.
        opp = [v for v in cls[1 - c] if len(adj[v]) < d]
        rng.shuffle(opp)
        for v in opp[:d]:
            adj[x].add(v)
            adj[v].add(x)

        cost = _bad(n, adj, D)
        found = cost == 0
        T = 1.0
        while not found and time.monotonic() < deadline:
            if rng.random() < 0.2:
                # Free addition: never increases the number of bad pairs.
                u = rng.randrange(n)
                if len(adj[u]) >= d:
                    continue
                w = rng.choice(cls[1 - colors[u]])
                if w in adj[u] or len(adj[w]) >= d:
                    continue
                adj[u].add(w)
                adj[w].add(u)
                cost = _bad(n, adj, D)
            else:
                # Rewire (u,v) -> (u,w) with w on the same side as v.
                u = rng.randrange(n)
                if not adj[u]:
                    continue
                v = rng.choice(list(adj[u]))
                w = rng.choice(cls[colors[v]])
                if w == u or w == v or w in adj[u] or len(adj[w]) >= d:
                    continue
                adj[u].discard(v)
                adj[v].discard(u)
                adj[u].add(w)
                adj[w].add(u)
                new_cost = _bad(n, adj, D)
                delta = new_cost - cost
                if delta <= 0 or rng.random() < math.exp(-delta / T):
                    cost = new_cost
                else:
                    adj[u].discard(w)
                    adj[w].discard(u)
                    adj[u].add(v)
                    adj[v].add(u)
            if cost == 0:
                found = True

        if not found:
            break

        edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
        if n > state['n'] and lib.is_valid(n, edges, d, D):
            state['n'] = n
            state['best'] = (n, edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.7 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)

    if D >= 3:
        try:
            cands = _arc_candidates(d, deadline, rng)
        except Exception:
            cands = []
        cands.sort(key=lambda t: -t[0])
        for n, e in cands:
            if n <= best[0]:
                break
            if lib.is_valid(n, e, d, D):
                best = (n, e)
                break

    # Skip the search when the baseline already meets the Moore bound (e.g. d=3, D=3).
    if (D >= 3 and d >= 3 and best[0] < lib._moore_bound(d, D)
            and time.monotonic() < deadline):
        state = {'n': best[0], 'best': best}
        try:
            _search(best[0], best[1], d, D, rng, deadline, state)
        except Exception:
            pass
        best = state['best']

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
