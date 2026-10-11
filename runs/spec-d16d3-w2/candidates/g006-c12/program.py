import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data.
# ----------------------------------------------------------------------------

def _pg_struct(q):
    """Return (m, edges, point_lines, line_points) for the incidence graph of PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


# ----------------------------------------------------------------------------
# Ruin-and-recreate search for an arc-like set S of points (new routine).
#
# S must satisfy: every line meets S in <= s points, and every point lies on
# <= s lines indexed by S (line j has the same coordinates as point j). Each
# iteration removes a few random members of S, then refills greedily in a random
# order. The move is kept if |S| does not drop (plateau moves allowed); otherwise
# it is undone, with an occasional small acceptance to escape local optima.
# ----------------------------------------------------------------------------

def _ruin_recreate(m, s, point_lines, line_points, S0, rng, deadline):
    cl = [0] * m          # extra degree on each line (number of S-points on it)
    cp = [0] * m          # extra degree on each point (number of S-lines through it)
    inS = [False] * m
    S = []

    def ok(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fill():
        order = [P for P in range(m) if not inS[P]]
        rng.shuffle(order)
        got = []
        for P in order:
            if ok(P):
                add(P)
                got.append(P)
        return got

    for P in S0:
        if not inS[P] and ok(P):
            add(P)
    fill()
    best = list(S)
    while time.monotonic() < deadline:
        size0 = len(S)
        r = rng.randint(1, min(len(S), 6)) if S else 0
        removed = rng.sample(S, r) if r else []
        for P in removed:
            rem(P)
        got = fill()
        if len(S) >= size0 or rng.random() < 0.01:
            if len(S) > len(best):
                best = list(S)
        else:
            for P in got:
                rem(P)
            for P in removed:
                add(P)
    return best


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG(2,q) incidence plus one new A-vertex per point of S and one new B-vertex per line of S."""
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


def _arc_family(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if lib.is_prime_power(q):
            s = d - q - 1
            if s >= 0:
                qs.append((q, s))
    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp = _pg_struct(q)
        if s == 0:
            out.append((2 * m, list(edges)))
            continue
        S = _ruin_recreate(m, s, pl, lp, [], rng, now + share)
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Diameter-preserving polish: twins and cross-side edge saturation.
# ----------------------------------------------------------------------------

def _twin_saturate(n, edges, d, D, rng, deadline):
    """Add twins of vertices whose neighbours all have spare degree (diameter <= D kept for D >= 2)."""
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


def _bipartition(n, adj):
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


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices. Adding such edges never increases distances."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
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

    def polish(n, e, budget):
        until = min(deadline, time.monotonic() + budget)
        n2, e2 = _twin_saturate(n, e, d, D, rng, until)
        return _saturate_edges(n2, e2, d, rng)

    if D >= 3:
        arc_deadline = start + 0.8 * (deadline - start)
        for n_c, e_c in _arc_family(d, arc_deadline, rng):
            consider(n_c, e_c)
            pn, pe = polish(n_c, e_c, 0.02 * time_limit)
            consider(pn, pe)

    pn, pe = polish(best[0], best[1], 0.02 * time_limit)
    consider(pn, pe)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
