import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic helpers
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_incidence(q):
    """PG(2,q) incidence data: m points, m lines, point_lines[P] and line_points[L]."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


# ----------------------------------------------------------------------------
# New helper: independent (dual) arc sets.
#
# An A-vertex attached to point P (P in S1) joins the lines through P, so each
# line may carry at most s such A-vertices. A B-vertex attached to line j
# (j in S2) joins the points on j, so each point may carry at most s such
# B-vertices. S1 and S2 are therefore constrained independently, and each side
# is searched with its own greedy pass (and the conic as a candidate).
# Every resulting graph is still checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _greedy_side(hit, m, s, rng, trials, deadline):
    """Randomised greedy: pick items i whose resource lists hit[i] stay below capacity s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for i in order:
            h = hit[i]
            if all(cnt[r] < s for r in h):
                S.append(i)
                for r in h:
                    cnt[r] += 1
        if len(S) > len(best):
            best = S
    return best


def _side_ok(S, hit, m, s):
    cnt = [0] * m
    for i in S:
        for r in hit[i]:
            cnt[r] += 1
            if cnt[r] > s:
                return False
    return True


def _conic_set(q, index):
    """Conic plus nucleus (q even). Valid as a point set and, by duality, as a line set."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _dual_graph(m, edges, point_lines, line_points, S1, S2):
    """PG(2,q) incidence plus A-vertices (indexed by S1 points) and B-vertices (indexed by S2 lines)."""
    k1, k2 = len(S1), len(S2)
    n = 2 * m + k1 + k2
    E = list(edges)
    for t, P in enumerate(S1):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S2):
        b = 2 * m + k1 + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k1 + [1] * k2
    return n, E, side


def _dual_candidates(d, deadline, rng):
    """For each prime power q with q+1 <= d, the best dual-arc extension of PG(2,q)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points = _pg_incidence(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}

        cand1 = [[]]
        cand2 = [[]]
        cand1.append(_greedy_side(point_lines, m, s, rng, 40, deadline))
        cand2.append(_greedy_side(line_points, m, s, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            cand1.append(cs)
            cand2.append(cs)
        S1 = max((c for c in cand1 if _side_ok(c, point_lines, m, s)), key=len)
        S2 = max((c for c in cand2 if _side_ok(c, line_points, m, s)), key=len)
        n, E, side = _dual_graph(m, edges, point_lines, line_points, S1, S2)
        out.append((n, E, side))
    return out


# ----------------------------------------------------------------------------
# Repair annealing (adds two vertices, one per side, then anneals).
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _apply(adj, ops):
    for op, x, y in ops:
        if op == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _propose(adj, side0, side1, d, rng):
    r = rng.random()
    if r < 0.6:
        x1 = rng.choice(side0)
        x2 = rng.choice(side0)
        if x1 == x2 or not adj[x1] or not adj[x2]:
            return None
        y1 = rng.choice(list(adj[x1]))
        y2 = rng.choice(list(adj[x2]))
        if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            return None
        return [('d', x1, y1), ('d', x2, y2), ('a', x1, y2), ('a', x2, y1)]
    if r < 0.8:
        x = rng.choice(side0)
        y = rng.choice(side1)
        if y in adj[x] or len(adj[x]) >= d or len(adj[y]) >= d:
            return None
        return [('a', x, y)]
    x1 = rng.choice(side0)
    if not adj[x1]:
        return None
    y1 = rng.choice(list(adj[x1]))
    if rng.random() < 0.5:
        y2 = rng.choice(side1)
        if y2 == y1 or y2 in adj[x1] or len(adj[y2]) >= d:
            return None
        return [('d', x1, y1), ('a', x1, y2)]
    x2 = rng.choice(side0)
    if x2 == x1 or y1 in adj[x2] or len(adj[x2]) >= d:
        return None
    return [('d', x1, y1), ('a', x2, y1)]


def _repair(n, adj, side, d, D, rng, deadline):
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    cost = _bad_pairs(n, adj, D)
    T = 1.5
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        T = max(0.1, T * 0.999)
        ops = _propose(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            undo = [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)]
            _apply(adj, undo)
    return True


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) for D = 4 (unchanged baseline).
# ----------------------------------------------------------------------------

def _gq_w(q):
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D == 2:
        return best_n, list(best_E)

    base = None
    if D >= 3:
        cands = _dual_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            if lib.is_valid(n_c, E_c, d, D):
                consider(n_c, E_c)
                if base is None:
                    base = (n_c, E_c, _side)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Repair search for D = 3: add two vertices (one per side) and anneal back to
    # diameter 3. Each success becomes the next starting point.
    if D == 3 and base is not None:
        n, E, side = base
        adj = _to_adj(n, E)
        side = list(side)
        while time.monotonic() < deadline:
            n_t = n + 2
            if n_t > _moore(d, D):
                break
            adj.append(set())
            adj.append(set())
            side = side + [0, 1]
            if not _repair(n_t, adj, side, d, D, rng, deadline):
                break
            E2 = [(x, y) for x in range(n_t) for y in adj[x] if x < y]
            if not lib.is_valid(n_t, E2, d, D):
                break
            consider(n_t, E2)
            n = n_t

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
