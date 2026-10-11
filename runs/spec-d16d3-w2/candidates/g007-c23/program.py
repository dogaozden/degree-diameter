import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: projective plane PG(2, q) plus arc extension (diameter 3).
# Each S-element P adds an A-vertex joined to the q+1 lines through P and a
# B-vertex joined to the q+1 points on line P. Loads are capped by s = d-q-1.
# ----------------------------------------------------------------------------

def _pg_lines(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _arc_search(m, s, point_lines, line_points, rng, deadline):
    """Randomized greedy plus plateau/swap local search for a large S with all loads <= s."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def can(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

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

    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if can(P):
            add(P)
    best = list(S)
    while time.monotonic() < deadline:
        for _ in range(200):
            P = rng.randrange(m)
            if inS[P]:
                continue
            if can(P):
                add(P)
            else:
                satL = {L for L in point_lines[P] if cl[L] >= s}
                satQ = {Q for Q in line_points[P] if cp[Q] >= s}
                B = [R for R in S
                     if any(L in satL for L in point_lines[R])
                     or any(Q in satQ for Q in line_points[R])]
                if len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
                    for R in B:
                        remove(R)
                    add(P)
            if len(S) > len(best):
                best = list(S)
    return best


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t          # A-vertex (side 0), joined to lines through P
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t      # B-vertex (side 1), joined to points on line j
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E


def _base_arc(d, deadline, rng):
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
    best = None
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp = _pg_lines(q)
        s = d - q - 1
        S = []
        if s >= 1:
            S = _arc_search(m, s, pl, lp, rng, now + share)
            if not _loads_ok(S, s, m, pl, lp):
                S = []
        n, E = _arc_graph(m, edges, pl, lp, S)
        if (best is None or n > best[0]) and lib.is_valid(n, E, d, 3):
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Structure helpers.
# ----------------------------------------------------------------------------

def _struct(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return adj, side


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _link(adj, u, v):
    adj[u].add(v)
    adj[v].add(u)


def _unlink(adj, u, v):
    adj[u].discard(v)
    adj[v].discard(u)


def _add_pair(adj, side, d, rng):
    """Append one new side-0 vertex and one new side-1 vertex, each joined to deficient vertices."""
    n = len(adj)
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    a, b = n, n + 1
    defB = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    defA = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    rng.shuffle(defB)
    rng.shuffle(defA)
    for v in defB[:d]:
        _link(adj, a, v)
    for v in defA[:d]:
        _link(adj, b, v)


# ----------------------------------------------------------------------------
# Repair annealing on a bipartite graph with degree cap d, minimising the
# number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
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


def _propose(n, side, adj, d, rng):
    """Apply a random move; return an undo callable, or None if no move was made."""
    if rng.random() < 0.3:
        defA = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
        defB = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
        if defA and defB:
            a = rng.choice(defA)
            b = rng.choice(defB)
            if b not in adj[a]:
                _link(adj, a, b)
                return lambda a=a, b=b: _unlink(adj, a, b)
    a = rng.randrange(n)
    if not adj[a]:
        return None
    b = rng.choice(list(adj[a]))
    if rng.random() < 0.5:
        keep, moved = a, b
    else:
        keep, moved = b, a
    _unlink(adj, keep, moved)
    cands = [v for v in range(n)
             if side[v] == side[moved] and v != moved
             and len(adj[v]) < d and v not in adj[keep]]
    if not cands:
        _link(adj, keep, moved)
        return None
    c = rng.choice(cands)
    _link(adj, keep, c)
    return lambda keep=keep, c=c, moved=moved: (_unlink(adj, keep, c),
                                                _link(adj, keep, moved))


def _anneal(n, side, adj, d, D, deadline, rng):
    """Drive the cost to zero; returns True on success. Modifies adj in place."""
    cur = _cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    misses = 0
    while cur > 0:
        now = time.monotonic()
        if now >= deadline or misses > 3000:
            return False
        T = 2.0 * (0.05 ** ((now - t0) / span))
        undo = _propose(n, side, adj, d, rng)
        if undo is None:
            misses += 1
            continue
        misses = 0
        new = _cost(n, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            undo()
    return True


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + min(0.85 * time_limit, time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    if D == 3 and d >= 3:
        base = _base_arc(d, start + 0.25 * time_limit, rng)
        if base is not None and base[0] > best_n:
            best_n, best_E = base

    # Grow by two vertices at a time, repairing with annealing.
    adj, side = _struct(best_n, best_E)
    cur_n = best_n
    while True:
        now = time.monotonic()
        remain = end - now
        if remain < 1.0:
            break
        if not any(len(a) < d for a in adj):
            break
        new_adj = [set(a) for a in adj]
        new_side = list(side)
        _add_pair(new_adj, new_side, d, rng)
        ok = _anneal(cur_n + 2, new_side, new_adj, d, D, now + 0.6 * remain, rng)
        if not ok:
            break
        cand = _edges(cur_n + 2, new_adj)
        if not lib.is_valid(cur_n + 2, cand, d, D):
            break
        adj, side, cur_n = new_adj, new_side, cur_n + 2
        best_n, best_E = cur_n, cand

    if not lib.is_valid(best_n, best_E, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_E
