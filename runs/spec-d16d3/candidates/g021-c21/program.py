import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and arc-extended incidence graphs (diameter 3).
#
# PG(2, q) incidence with spare capacity s = d - q - 1 per vertex. Choose a
# point set S whose lines carry at most s points of S and whose points lie on
# at most s lines of S. Add an A-vertex per point of S (joined to its lines)
# and a B-vertex per line of S (joined to its points). Diameter stays 3.
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus A (point side) and B (line side) vertices per element of S."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """Return (n, edges, side) candidates: plain PG incidence and arc extensions per prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        out.append((2 * m, list(edges), [0] * m + [1] * m))
        if s < 1:
            continue
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New helper: spare-degree vertex insertion + degree-preserving repair annealing.
#
# Insert a vertex on one side, joined to up to d spare vertices of the other
# side, chosen greedily to maximise coverage of radius-2 balls (so that the new
# vertex is close to as many vertices as possible). The graph then has a few
# bad pairs. Repair them by annealing over moves that keep the bipartition:
#   * double edge swap (keeps every degree),
#   * edge addition between spare vertices (never increases the bad-pair count),
#   * endpoint moves that shift an edge to a vertex with spare capacity.
# Cost = number of unordered pairs at distance > D. Zero means valid.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts as bad)."""
    reach = _balls(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _insert(adj, side, d, rng):
    """Append one vertex joined to <= d spare vertices of the opposite side, greedy by radius-2 coverage."""
    n = len(adj)
    c = rng.randrange(2)
    pool = [v for v in range(n) if side[v] != c and len(adj[v]) < d]
    if not pool:
        return False
    ball = _balls(n, adj, 2)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        top = max(gains)
        if top == 0:
            break
        thr = top - (1 if rng.random() < 0.3 else 0)
        opts = [i for i, g in enumerate(gains) if g >= max(thr, 1)]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    if not chosen:
        return False
    v = n
    adj.append(set(chosen))
    side.append(c)
    for s in chosen:
        adj[s].add(v)
    return True


def _link(adj, a, b):
    adj[a].add(b)
    adj[b].add(a)


def _unlink(adj, a, b):
    adj[a].discard(b)
    adj[b].discard(a)


def _anneal(adj, side, d, D, rng, t_stop, budget):
    """Degree-respecting annealing on bad-pair count. Returns final cost (0 means valid)."""
    n = len(adj)
    cost = _bad(n, adj, D)
    S0 = [v for v in range(n) if side[v] == 0]
    S1 = [v for v in range(n) if side[v] == 1]
    T0, T1 = 2.0, 0.15
    t_start = time.monotonic()
    while cost > 0:
        now = time.monotonic()
        if now >= t_stop:
            break
        frac = min(1.0, (now - t_start) / max(budget, 1e-3))
        T = T0 * (T1 / T0) ** frac
        r = rng.random()
        if r < 0.25:
            # edge addition between spare vertices: never increases the cost
            a = rng.choice(S0)
            b = rng.choice(S1)
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            _link(adj, a, b)
            cost = _bad(n, adj, D)
        elif r < 0.65:
            # double edge swap: (a,b),(c,e) -> (a,e),(c,b); all degrees preserved
            a = rng.choice(S0)
            c = rng.choice(S0)
            if a == c or not adj[a] or not adj[c]:
                continue
            b = rng.choice(tuple(adj[a]))
            e = rng.choice(tuple(adj[c]))
            if b == e or e in adj[a] or b in adj[c]:
                continue
            _unlink(adj, a, b)
            _unlink(adj, c, e)
            _link(adj, a, e)
            _link(adj, c, b)
            c2 = _bad(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                _unlink(adj, a, e)
                _unlink(adj, c, b)
                _link(adj, a, b)
                _link(adj, c, e)
        else:
            # endpoint move: shift one end of an edge to a vertex with spare capacity
            a = rng.choice(S0)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            if rng.random() < 0.5:
                a2 = rng.choice(S0)
                if a2 == a or b in adj[a2] or len(adj[a2]) >= d:
                    continue
                _unlink(adj, a, b)
                _link(adj, a2, b)
                c2 = _bad(n, adj, D)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    _unlink(adj, a2, b)
                    _link(adj, a, b)
            else:
                b2 = rng.choice(S1)
                if b2 == b or b2 in adj[a] or len(adj[b2]) >= d:
                    continue
                _unlink(adj, a, b)
                _link(adj, a, b2)
                c2 = _bad(n, adj, D)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    _unlink(adj, a, b2)
                    _link(adj, a, b)
    return cost


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    fallback = (best_n, best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D < 3:
        return fallback

    # Starting bases: plain PG and arc-extended PG graphs, largest first.
    cands = _arc_candidates(d, t0 + 0.2 * time_limit, rng)
    cands.sort(key=lambda c: -c[0])
    for n_c, e_c, _ in cands:
        consider(n_c, e_c)

    # Repair growth: insert a vertex with spare neighbours, then anneal back to diameter D.
    if cands:
        n0, e0, s0 = cands[0]
        if lib.is_valid(n0, e0, d, D):
            adj = [set() for _ in range(n0)]
            for u, v in e0:
                adj[u].add(v)
                adj[v].add(u)
            cur_adj, cur_side = adj, list(s0)
            fails = 0
            while fails < 8 and time.monotonic() < end - 1.0:
                work = [set(x) for x in cur_adj]
                sd = list(cur_side)
                if not _insert(work, sd, d, rng):
                    break
                budget = min(12.0, end - time.monotonic())
                if budget <= 0.5:
                    break
                cost = _anneal(work, sd, d, D, rng, time.monotonic() + budget, budget)
                if cost == 0:
                    cur_adj, cur_side = work, sd
                    fails = 0
                    n2 = len(work)
                    e_new = [(u, v) for u in range(n2) for v in work[u] if u < v]
                    consider(n2, e_new)
                else:
                    fails += 1

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
