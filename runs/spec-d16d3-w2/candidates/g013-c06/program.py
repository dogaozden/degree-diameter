import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line meets S in at most
# s points and every point lies on at most s lines indexed by S. For each P in
# S add a new A-vertex joined to the lines through P; for each j in S add a new
# B-vertex joined to the points on line j. Order 2m + 2|S|.
#
# Candidate arcs come from randomized greedy selection and, for s >= 2, from a
# conic (plus nucleus when q is even).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, pl, lp, index) for PG(2, q). pl[P] = lines through P, lp[L] = points on L."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, pl, lp, index


def _loads_ok(S, s, m, pl, lp):
    """True if every line meets S in <= s points and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy arc with all loads <= s; returns the largest found."""
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
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


def _arc_graph(m, edges, S, pl, lp):
    """Old incidence plus one A-vertex and one B-vertex per element of S. Ids are dense."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _arc_for_q(d, q, rng, deadline):
    """Build the arc-extended graph for PG(2, q) under degree d. Returns (n, E, m, pl, lp)."""
    m, edges, pl, lp, index = _pg(q)
    s = d - q - 1
    S = []
    if s >= 1:
        S = _greedy_arc(m, s, pl, lp, rng, 30, deadline)
    if s >= 2:
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
            S = cs
    if not _loads_ok(S, s, m, pl, lp):
        S = []
    n, E = _arc_graph(m, edges, S, pl, lp)
    return n, E, m, pl, lp


# ----------------------------------------------------------------------------
# Validity-checked annealing on the arc graph (D = 3 target).
#
# State: adjacency sets. Moves:
#   * add a vertex adjacent to a star (lines through a point, or points on a
#     line) using only neighbours with spare degree;
#   * remove a random vertex.
# A move is kept only if the result passes lib.is_valid, so every accepted
# state is valid. The best valid state is returned.
# ----------------------------------------------------------------------------

def _search(n0, E0, m, pl, lp, d, D, deadline, rng):
    adj = {}

    def link(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)

    def unlink(v):
        nb = adj.pop(v, set())
        for u in nb:
            s = adj.get(u)
            if s is not None:
                s.discard(v)
                if not s:
                    del adj[u]
        return nb

    def restore(v, nb):
        if nb:
            adj[v] = set(nb)
            for u in nb:
                adj.setdefault(u, set()).add(v)

    def raw():
        return [(u, v) for u in adj for v in adj[u] if u < v]

    def valid():
        n, E = lib.relabel(raw())
        return lib.is_valid(n, E, d, D)

    for u, v in E0:
        link(u, v)

    nxt = n0
    best = raw()
    best_cnt = len(adj)
    cur = len(adj)
    T = 0.5

    while time.monotonic() < deadline:
        if rng.random() < 0.6:
            c = rng.randrange(2 * m)
            cand = [m + L for L in pl[c]] if c < m else list(lp[c - m])
            nb = [u for u in cand if u in adj and len(adj[u]) < d]
            if len(nb) < 2:
                continue
            x = nxt
            nxt += 1
            for u in nb:
                link(x, u)
            undo = (lambda x=x: unlink(x))
            delta = 1
        else:
            if not adj:
                continue
            v = rng.choice(list(adj))
            nb = unlink(v)
            undo = (lambda v=v, nb=nb: restore(v, nb))
            delta = -1

        if delta < 0 and rng.random() >= math.exp(delta / T):
            undo()
            continue
        if not valid():
            undo()
            continue

        cur = len(adj)
        if cur > best_cnt:
            best_cnt = cur
            best = raw()
        elif cur < best_cnt - 6:
            # Drifted too far below the best: restart from the best state.
            adj.clear()
            for u, v in best:
                link(u, v)

    n, E = lib.relabel(best)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    best = (fb_n, fb_E)
    if D == 2:
        return best

    # Arc-extended PG(2, q) graphs: diameter 3, so valid for all D >= 3.
    arcs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > start + 0.3 * time_limit:
            break
        try:
            n, E, m, pl, lp = _arc_for_q(d, q, rng, start + 0.3 * time_limit)
        except Exception:
            continue
        arcs.append((n, E, m, pl, lp))
    arcs.sort(key=lambda t: -t[0])

    chosen = None
    for n, E, m, pl, lp in arcs:
        if lib.is_valid(n, E, d, D):
            if n > best[0]:
                best = (n, E)
            if chosen is None:
                chosen = (n, E, m, pl, lp)
            break

    # Local search from the largest valid arc graph, only if it has extension vertices.
    if chosen is not None and chosen[0] > 2 * chosen[2]:
        try:
            n_c, E_c, m, pl, lp = chosen
            res = _search(n_c, E_c, m, pl, lp, d, D, deadline, rng)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fb_n, fb_E
    return best
