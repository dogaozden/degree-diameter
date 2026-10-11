"""Projective-plane arc-pair family for diameter-3 bipartite graphs.

Base: incidence graph of PG(2, q), q the largest prime power with q + 1 <= d.
Extension: choose two independent point/line sets S1, S2 with S1 holding at most
s = d - q - 1 points on each line and S2 holding at most s lines through each point.
Add one new point-side vertex x_P per P in S1 (joined to the q+1 lines through P)
and one new line-side vertex y_L per L in S2 (joined to the q+1 points on L).
The degree bookkeeping keeps every vertex at most d, and diameter 3 is preserved.
Afterwards, greedy cover extension adds further vertices whose radius-(D-1)
balls cover the graph.

Every candidate is checked with lib.is_valid before it can win, and K_{d,d}
(valid for D >= 2) is the fallback, so the program always returns a valid graph.
This family alone reaches 2m + 2*|arc| (394 for d = 16), and the arc bound caps it
there, so beating 394 depends on the cover-extension step. That step is not
guaranteed to find extra vertices.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane data.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, pl, lp): incidence graph of PG(2, q) plus point->line and line->point lists."""
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    pl = [[] for _ in range(m)]   # point -> lines (line indices 0..m-1)
    lp = [[] for _ in range(m)]   # line -> points
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _conic(q):
    """Point indices of a conic (plus nucleus for even q); no three collinear, a good seed arc."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _best_q(d):
    """Largest prime power q with q + 1 <= d (the PG degree must fit), or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# Arc search: a set S of elements such that every constraint is loaded at most s.
# cons[x] lists the constraint ids touched by element x.
# ----------------------------------------------------------------------------

def _arc_search(m, s, cons, rng, deadline, init):
    """Iterated local search for a large S with all loads <= s, seeded from init."""
    load = [0] * m
    inS = [False] * m
    S = []

    def add(x):
        inS[x] = True
        S.append(x)
        for c in cons[x]:
            load[c] += 1

    def rem(x):
        inS[x] = False
        S.remove(x)
        for c in cons[x]:
            load[c] -= 1

    for x in init:
        if not inS[x] and all(load[c] < s for c in cons[x]):
            add(x)
    best = list(S)
    while time.monotonic() < deadline:
        x = rng.randrange(m)
        if inS[x]:
            continue
        sat = {c for c in cons[x] if load[c] >= s}
        if not sat:
            add(x)
        else:
            B = [r for r in S if any(c in sat for c in cons[r])]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
                for r in B:
                    rem(r)
                add(x)
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(m, edges, pl, lp, S1, S2):
    """PG incidence plus x-vertices (points of S1, adjacent to lines) and y-vertices (lines of S2, adjacent to points)."""
    n = 2 * m + len(S1) + len(S2)
    E = list(edges)
    for t, P in enumerate(S1):
        x = 2 * m + t
        E.extend((x, m + L) for L in pl[P])
    base = 2 * m + len(S1)
    for t, L in enumerate(S2):
        y = base + t
        E.extend((Q, y) for Q in lp[L])
    return n, E


# ----------------------------------------------------------------------------
# Cover-based vertex extension: a new vertex z joined to a set T on the
# opposite side, where the radius-(D-1) balls of T cover every vertex.
# ----------------------------------------------------------------------------

def _color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
    return col


def _ball(n, adj, r):
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


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidate balls; None on failure."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d:
        best, bg = None, 0
        for s in pool:
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                bg, best = g, s
        if best is None:
            break
        chosen.append(best)
        pool.remove(best)
        covered |= ball[best]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Repeatedly add a cover vertex while one exists within the deadline."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _color(n, adj)
    while time.monotonic() < deadline:
        ball = _ball(n, adj, D - 1)
        full = (1 << n) - 1
        grown = False
        for c in rng.sample([0, 1], 2):
            if time.monotonic() >= deadline:
                break
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(20):
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                adj.append([])
                color.append(1 - c)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Plain PG(2, q) incidence graph: diameter 3, valid for every D >= 3.
    q0 = _best_q(d)
    if q0 is None:
        return best
    m0, e0, _, _ = _pg(q0)
    consider(2 * m0, e0)

    # Arc-pair family, one entry per prime power q with spare degree s >= 1.
    arcs = []
    for q in range(2, d):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp = _pg(q)
        cap = 2 * m + 2 * (s * m // (q + 1))  # counting bound on the new order
        if cap <= best_n:
            continue
        try:
            cone = _conic(q)
        except Exception:
            cone = []
        arcs.append((cap, q, s, m, edges, pl, lp, cone))
    arcs.sort(key=lambda t: -t[0])

    rounds = 0
    while time.monotonic() < deadline and arcs:
        for cap, q, s, m, edges, pl, lp, cone in arcs:
            if time.monotonic() >= deadline:
                break
            if cap <= best_n:
                continue
            slice_end = min(deadline, time.monotonic() + 0.7)
            init = cone if rounds == 0 else []
            S1 = _arc_search(m, s, pl, rng, slice_end, init)
            S2 = _arc_search(m, s, lp, rng, slice_end, init)
            if not S1 and not S2:
                continue
            n, e = _arc_graph(m, edges, pl, lp, S1, S2)
            consider(n, e)
            n2, e2 = _extend_cover(n, e, d, D,
                                   min(deadline, time.monotonic() + 1.5), rng)
            consider(n2, e2)
        rounds += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
