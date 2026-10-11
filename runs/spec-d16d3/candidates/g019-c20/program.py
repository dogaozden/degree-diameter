"""Projective-plane twin extension with independent capped sets.

New idea in this version: the parent used one point set S for both the new A-vertices
(twins of points) and the new B-vertices (twins of lines). Here the two sets are chosen
independently. S is a set of points with at most s points on any line, and T is a set of
lines with at most s lines through any point, where s = d - (q+1) is the spare degree.
Both are found by a capped local search with plateau swaps and random restarts.

Diameter 3 is kept for any such choice: A_P reaches every point in 2 steps and every line
in 3 steps, and B_L does the same by duality. Adding edges between opposite colour classes
never increases distances, so the final saturation pass is also safe.

Honest note: for d = 16 the twin family is capped at 2(q^2+q+1) + 2(q+1) = 394 with q = 13.
Any new vertex within distance 3 of the whole graph must have a line-blocking neighbourhood,
and the smallest nontrivial blocking set in PG(2,13) has more than 16 points. Beating 394
therefore needs a construction outside this family; this program does not claim to do that.
"""
import random
import time

import lib


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points are 0..m-1, lines are 0..m-1 too."""
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _capped_set(m, res_of, users_of, s, rng, iters, deadline):
    """Largest-found set E of elements 0..m-1 such that every resource is used at most s times.

    res_of[e] lists the resources used by element e. users_of[r] lists the elements using r.
    Moves: add a feasible element, or evict one member that shares a full resource and
    insert the new element if that makes it feasible (a plateau move of equal size).
    """
    nres = len(users_of)
    load = [0] * nres
    inS = [False] * m
    S = []

    def feasible(e):
        for r in res_of[e]:
            if load[r] >= s:
                return False
        return True

    def add(e):
        inS[e] = True
        S.append(e)
        for r in res_of[e]:
            load[r] += 1

    def remove(e):
        inS[e] = False
        S.remove(e)
        for r in res_of[e]:
            load[r] -= 1

    order = list(range(m))
    rng.shuffle(order)
    for e in order:
        if feasible(e):
            add(e)
    best = list(S)
    for it in range(iters):
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        e = rng.randrange(m)
        if inS[e]:
            continue
        if feasible(e):
            add(e)
        else:
            full = [r for r in res_of[e] if load[r] >= s]
            r = rng.choice(full)
            members = [f for f in users_of[r] if inS[f]]
            f = rng.choice(members)
            remove(f)
            if feasible(e):
                add(e)
            else:
                add(f)
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _bi_arc_search(m, s, point_lines, line_points, rng, deadline, iters):
    """Independently search S (points, line-load <= s) and T (lines, point-load <= s)."""
    best_S, best_T = [], []
    first = True
    while first or time.monotonic() < deadline:
        first = False
        S = _capped_set(m, point_lines, line_points, s, rng, iters, deadline)
        T = _capped_set(m, line_points, point_lines, s, rng, iters, deadline)
        if len(S) + len(T) > len(best_S) + len(best_T):
            best_S, best_T = S, T
    return best_S, best_T


def _bi_arc_graph(m, edges, point_lines, line_points, S, T):
    """Old incidence graph plus an A-twin for each point of S and a B-twin for each line of T."""
    base = 2 * m
    n = base + len(S) + len(T)
    E = list(edges)
    for t, P in enumerate(S):
        a = base + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, L in enumerate(T):
        b = base + len(S) + t
        for Q in line_points[L]:
            E.append((Q, b))
    colors = [0] * m + [1] * m + [0] * len(S) + [1] * len(T)
    return n, E, colors


def _saturate(n, color, edges, d, rng):
    """Greedily add random opposite-colour edges between vertices with spare degree."""
    E = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best, best_n = fallback, fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    if D == 2:
        return best

    # Plain projective planes (diameter 3) and the spare-degree twin extensions.
    arc_jobs = []
    for q in range(d - 1, 1, -1):
        if not lib.is_prime_power(q):
            continue
        m, edges, pl, lp = _pg_data(q)
        consider(2 * m, edges)
        s = d - q - 1
        if s >= 1:
            arc_jobs.append((2 * m, q, m, edges, pl, lp, s))

    if arc_jobs:
        arc_jobs.sort(key=lambda job: -job[0])
        remaining = max(0.0, deadline - time.monotonic())
        # The largest candidate gets half the budget; the rest is split evenly.
        shares = [0.5 * remaining] + [0.5 * remaining / (len(arc_jobs) - 1)] * (len(arc_jobs) - 1) \
            if len(arc_jobs) > 1 else [remaining]
        for share, (_, q, m, edges, pl, lp, s) in zip(shares, arc_jobs):
            dl = time.monotonic() + share
            S, T = _bi_arc_search(m, s, pl, lp, rng, dl, 20000)
            n, E, colors = _bi_arc_graph(m, edges, pl, lp, S, T)
            consider(n, _saturate(n, colors, E, d, rng))
            if best_n < n:
                consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
