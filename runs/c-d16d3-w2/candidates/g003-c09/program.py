import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 (kept from parent, validated): arc-extended projective plane graphs.
# Incidence graph of PG(2, q) plus, for each point set SA and line set SB of
# bounded load, one new vertex per member. Diameter 3, bipartite by construction.
#
# Stage 2 (new, bold): fixed-order simulated-annealing rewiring. Starting from
# the best arc graph, add ONE vertex, then anneal over edge rewirings (targeted
# at pairs still at distance > D) until every pair is within distance D. This
# does not rely on any algebraic structure of the extension, so it can find
# graphs the arc construction cannot express. Each accepted graph is re-checked
# with lib.is_valid. If anything fails, the best valid graph so far is returned.
# ----------------------------------------------------------------------------

_LS_ITERS = 20000
_REPAIR_ITERS = 4000


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy selection under the load constraint."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau / improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus new A-vertices (colour 0) and B-vertices (colour 1)."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    col = [0] * m + [1] * m + [0] * na + [1] * nb
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, col


def _arc_candidates(d, rng, deadline):
    """Arc-extended graphs (n, edges, col) for prime powers q + 1 <= d, largest first."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 40, deadline)
        SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        SA = _local_search(m, s, pl, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, lp, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    out.sort(key=lambda t: -t[0])
    return out


# ----------------------------------------------------------------------------
# Stage 2: fixed-order rewiring annealer.
# ----------------------------------------------------------------------------

def _balls(N, adj, D):
    """Bitmask of vertices within distance D of each vertex."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        cur = reach
        reach = []
        for v in range(N):
            r = cur[v]
            for u in adj[v]:
                r |= cur[u]
            reach.append(r)
    return reach


def _bad(reach, N):
    """Number of unordered pairs at distance > D."""
    return sum(N - r.bit_count() for r in reach) // 2


def _edge_list(N, adj):
    return [(u, v) for u in range(N) for v in sorted(adj[u]) if u < v]


def _repair(N, col, adj, d, D, deadline, rng, iters):
    """Anneal edge rewirings at fixed order N until every pair is within distance D.

    adj is a list of sets, modified in place. Each move adds an edge (x, y) of
    opposite colours, removing one random edge at x and/or y if they are full,
    so degrees stay <= d. Moves are aimed at vertices with unreached pairs.
    Returns True iff the graph reaches zero bad pairs.
    """
    full = (1 << N) - 1
    opp = [[v for v in range(N) if col[v] == 0], [v for v in range(N) if col[v] == 1]]
    if not opp[0] or not opp[1]:
        return False
    reach = _balls(N, adj, D)
    cost = _bad(reach, N)
    T = 0.6
    for it in range(iters):
        if cost == 0:
            return True
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        cand = [v for v in range(N) if reach[v] != full]
        if not cand:
            break
        x = rng.choice(cand)
        miss = full ^ reach[x]
        other = opp[1 - col[x]]
        us = [u for u in other if (miss >> u) & 1]
        if not us:
            us = other
        y = rng.choice(us)
        if y in adj[x]:
            continue
        rem = []
        if len(adj[x]) >= d:
            rem.append((x, rng.choice(tuple(adj[x]))))
        if len(adj[y]) >= d:
            rem.append((rng.choice(tuple(adj[y])), y))
        for a, b in rem:
            adj[a].discard(b)
            adj[b].discard(a)
        adj[x].add(y)
        adj[y].add(x)
        new_reach = _balls(N, adj, D)
        new_cost = _bad(new_reach, N)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            reach, cost = new_reach, new_cost
        else:
            adj[x].discard(y)
            adj[y].discard(x)
            for a, b in rem:
                adj[a].add(b)
                adj[b].add(a)
        T = max(0.15, T * 0.9995)
    return cost == 0


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fb_n, fb_E = lib.haar_graph(d, range(d))
    fb_col = [0] * d + [1] * d
    best = (fb_n, fb_E)
    if D < 3 or d < 3:
        return best

    rng = random.Random(seed * 1000003 + d * 97 + D)
    arc_deadline = t0 + 0.3 * time_limit
    aug_deadline = t0 + 0.8 * time_limit
    moore = lib.moore_bound(d, D)

    # Stage 1: arc-extended PG graphs (diameter 3, valid for D >= 3).
    cur_n, cur_E, cur_col = fb_n, fb_E, fb_col
    cands = _arc_candidates(d, rng, arc_deadline)
    for n_c, e_c, col_c in cands:
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            cur_n, cur_E, cur_col = n_c, e_c, col_c
            break  # candidates are sorted, so the first valid one is largest

    # Stage 2: grow by one vertex at a time, repairing with annealed rewiring.
    while cur_n < moore and time.monotonic() < aug_deadline:
        N = cur_n + 1
        improved = False
        for _ in range(3):
            if time.monotonic() > aug_deadline:
                break
            adj = [set() for _ in range(N)]
            for u, v in cur_E:
                adj[u].add(v)
                adj[v].add(u)
            col = cur_col + [rng.randrange(2)]
            if _repair(N, col, adj, d, D, aug_deadline, rng, _REPAIR_ITERS):
                E = _edge_list(N, adj)
                if lib.is_valid(N, E, d, D):
                    cur_n, cur_E, cur_col = N, E, col
                    improved = True
                break
        if not improved:
            break

    if cur_n > best[0]:
        best = (cur_n, cur_E)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return (fb_n, fb_E)
