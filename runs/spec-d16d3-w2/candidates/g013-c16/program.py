import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. For a point set S with every line through at most s points
# of S and every point on at most s lines indexed by S, add a new A-vertex
# joined to the q+1 lines through each P in S, and a new B-vertex joined to
# the q+1 points on each line j in S. Order 2(q^2+q+1) + 2|S|.
#
# NEW: after the arc is fixed, an iterated local search (ILS) grows the graph.
# A new vertex x with neighbour set N keeps the diameter bound D iff every
# existing vertex is within distance D-1 of N. So growth is a set-cover
# problem: greedily pick neighbours with spare degree that cover the most
# still-uncovered vertices (bitmask balls). Vertex additions never break
# existing distances, so only removal kicks need a full validity check.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _arc(q, d, rng, deadline):
    """Return (S, m, edges, pl, lp) with S the largest arc found for PG(2, q) under capacity d."""
    s = d - q - 1
    m, edges, pl, lp = _pg(q)
    if s < 1:
        return [], m, edges, pl, lp
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    best = []
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        conic.append(index[(0, 1, 0)])
    if _loads_ok(conic, s, m, pl, lp):
        best = conic
    order = list(range(m))
    for _ in range(30):
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
    return best, m, edges, pl, lp


def _arc_graph(q, S, m, edges, pl, lp):
    """Return (n, edges, side) for the arc-extended graph. side[v] is 0 or 1 (bipartition)."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return 2 * m + 2 * k, E, side


# ----------------------------------------------------------------------------
# Bitmask balls and iterated local search.
# ----------------------------------------------------------------------------

def _balls(adj, R):
    """Per vertex, a bitmask of all vertices within distance R (dead vertices have no edges)."""
    N = len(adj)
    reach = [1 << v for v in range(N)]
    for _ in range(R):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _ils(n, edges, side, d, D, deadline, rng):
    """Iterated local search: greedy set-cover insertions plus remove-and-repair kicks.

    Returns (best_count, best_edges) with raw (uncompacted) vertex ids. Every returned graph
    is valid: insertions only add vertices that keep all pairs within D, and kicks are
    fully re-checked before acceptance.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    alive = [True] * n
    side = list(side)

    def edge_list():
        return [(u, v) for u in range(len(adj)) if alive[u] for v in adj[u] if u < v]

    def alive_mask():
        mask = 0
        for v in range(len(alive)):
            if alive[v]:
                mask |= 1 << v
        return mask

    def try_insert(B, am):
        """Add one vertex covering all alive vertices within distance D-1 of its neighbours."""
        s = rng.randrange(2)
        cand = [u for u in range(len(adj)) if alive[u] and side[u] != s and len(adj[u]) < d]
        if not cand:
            return False
        rng.shuffle(cand)
        unc = am
        chosen = []
        cs = set()
        while unc and len(chosen) < d:
            bu = -1
            bg = 0
            for u in cand:
                if u in cs:
                    continue
                g = (B[u] & unc).bit_count()
                if g > bg:
                    bg = g
                    bu = u
            if bu < 0:
                break
            chosen.append(bu)
            cs.add(bu)
            unc &= ~B[bu]
        if unc or not chosen:
            return False
        x = len(adj)
        adj.append(set(chosen))
        alive.append(True)
        side.append(s)
        for u in chosen:
            adj[u].add(x)
        return True

    cur = sum(alive)
    best_cnt = cur
    best_edges = edge_list()
    B = _balls(adj, D - 1)
    am = alive_mask()

    while time.monotonic() < deadline:
        if try_insert(B, am):
            cur += 1
            if cur > best_cnt:
                best_cnt = cur
                best_edges = edge_list()
            B = _balls(adj, D - 1)
            am = alive_mask()
            continue

        # Kick: remove a random vertex, then try to repair with up to 3 insertions.
        snap_adj = [set(a) for a in adj]
        snap_alive = list(alive)
        snap_side = list(side)
        alive_ids = [w for w in range(len(alive)) if alive[w]]
        victim = rng.choice(alive_ids)
        for u in adj[victim]:
            adj[u].discard(victim)
        adj[victim] = set()
        alive[victim] = False
        cnt = cur - 1
        B2 = _balls(adj, D - 1)
        am2 = alive_mask()
        for _ in range(3):
            if not try_insert(B2, am2):
                break
            cnt += 1
            B2 = _balls(adj, D - 1)
            am2 = alive_mask()

        Bd = _balls(adj, D)
        amf = alive_mask()
        ok = all((Bd[w] & amf) == amf for w in range(len(alive)) if alive[w])
        if ok and (cnt >= cur or rng.random() < 0.05):
            cur = cnt
            if cur > best_cnt:
                best_cnt = cur
                best_edges = edge_list()
        else:
            adj[:] = snap_adj
            alive[:] = snap_alive
            side[:] = snap_side
        B = _balls(adj, D - 1)
        am = alive_mask()

    return best_cnt, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3 or d < 3:
        return best

    def consider(n, E):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, E, d, D):
            best = (n, E)
            best_n = n

    # Arc-extended PG(2, q) graphs for every prime power q with q + 1 <= d.
    arcs = []
    arc_deadline = start + 0.2 * time_limit
    for q in range(2, d):
        if time.monotonic() > arc_deadline:
            break
        if not lib.is_prime_power(q):
            continue
        S, m, edges, pl, lp = _arc(q, d, rng, arc_deadline)
        n, E, side = _arc_graph(q, S, m, edges, pl, lp)
        consider(n, E)
        arcs.append((n, E, side))

    # ILS from the largest arc graph (valid for every D >= 3).
    if arcs:
        arcs.sort(key=lambda t: -t[0])
        n, E, side = arcs[0]
        _, raw_edges = _ils(n, E, side, d, D, deadline, rng)
        nn, EE = lib.relabel(raw_edges)
        consider(nn, EE)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
