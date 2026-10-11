import math
import random
import time

import lib


def _fallback(d):
    # K_{d,d}: bipartite, degree d, diameter 2.
    return lib.haar_graph(d, range(d))


def _pick_q(d):
    # Largest prime power q with q + 1 <= d (PG(2, q) has degree q + 1).
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg(q):
    """Incidence graph of PG(2, q). Points are 0..m-1, lines are m..2m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]   # point -> ids of lines through it
    line_points = [[] for _ in range(m)]   # line index -> ids of points on it
    for u, v in edges:
        point_lines[u].append(v)
        line_points[v - m].append(u)
    return m, point_lines, line_points, edges


def _edge_list(nbr):
    return [(u, v) for u in range(len(nbr)) for v in nbr[u] if u < v]


def _propose(nbr, side, m, point_lines, line_points, d, rng):
    """Mutate the graph in place and return an undo record.

    Move A: append a new vertex whose neighbourhood is a pencil (all lines through
    a point, or all points on a line). Saturated targets lose one random edge first.
    Move B: double-edge swap that keeps the vertex count and the degree bound.
    """
    n = len(nbr)
    if rng.random() < 0.7:
        if rng.random() < 0.5:
            targets = list(point_lines[rng.randrange(m)])
            new_side = 0
        else:
            targets = list(line_points[rng.randrange(m)])
            new_side = 1
        removed = []
        for t in targets:
            if len(nbr[t]) >= d:
                w = rng.choice(sorted(nbr[t]))
                nbr[t].discard(w)
                nbr[w].discard(t)
                removed.append((t, w))
        new = n
        nbr.append(set(targets))
        side.append(new_side)
        for t in targets:
            nbr[t].add(new)
        return ("add", new, targets, removed)

    xs = [v for v in range(n) if side[v] == 0 and nbr[v]]
    if not xs:
        return ("noop",)
    x = rng.choice(xs)
    y = rng.choice(sorted(nbr[x]))
    nbr[x].discard(y)
    nbr[y].discard(x)
    spx = [v for v in range(n) if side[v] == 0 and len(nbr[v]) < d]
    spy = [v for v in range(n) if side[v] == 1 and len(nbr[v]) < d]
    pair = None
    if spx and spy:
        for _ in range(12):
            x2 = rng.choice(spx)
            y2 = rng.choice(spy)
            if y2 not in nbr[x2]:
                pair = (x2, y2)
                break
    if pair is None:
        nbr[x].add(y)
        nbr[y].add(x)
        return ("noop",)
    x2, y2 = pair
    nbr[x2].add(y2)
    nbr[y2].add(x2)
    return ("swap", x, y, x2, y2)


def _undo(nbr, side, rec):
    kind = rec[0]
    if kind == "add":
        _, new, targets, removed = rec
        for t in targets:
            nbr[t].discard(new)
        nbr.pop()
        side.pop()
        for t, w in removed:
            nbr[t].add(w)
            nbr[w].add(t)
    elif kind == "swap":
        _, x, y, x2, y2 = rec
        nbr[x2].discard(y2)
        nbr[y2].discard(x2)
        nbr[x].add(y)
        nbr[y].add(x)
    # "noop": nothing to undo


def _search(d, D, q, deadline, rng):
    """Simulated annealing over graphs with max degree d, maximising order subject to diameter D.

    Energy = (bad pairs) - w * (order). The best state with zero bad pairs is kept.
    """
    m, point_lines, line_points, base = _pg(q)
    n = 2 * m
    nbr = [set() for _ in range(n)]
    side = [0] * m + [1] * m
    for u, v in base:
        nbr[u].add(v)
        nbr[v].add(u)

    cur_n, cur_bad = n, 0
    best_n, best_edges = n, list(base)
    w = 2.0
    T = 1.0
    while time.monotonic() < deadline:
        rec = _propose(nbr, side, m, point_lines, line_points, d, rng)
        n2 = len(nbr)
        edges = _edge_list(nbr)
        nb = lib.bad_pairs(n2, edges, D) if edges else 0
        dE = (nb - w * n2) - (cur_bad - w * cur_n)
        if dE <= 0 or rng.random() < math.exp(-dE / T):
            cur_bad, cur_n = nb, n2
            if nb == 0 and n2 > best_n:
                best_n, best_edges = n2, edges
        else:
            _undo(nbr, side, rec)
        T = max(0.05, T * 0.999)
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]
    fb = _fallback(d)
    if D == 2 or d < 3:
        return fb

    q = _pick_q(d)
    if q is None:
        return fb

    try:
        rng = random.Random(seed)
        deadline = start + 0.75 * time_limit
        n_best, e_best = _search(d, D, q, deadline, rng)
        if n_best > fb[0] and lib.is_valid(n_best, e_best, d, D):
            return n_best, e_best
    except Exception:
        pass
    return fb
