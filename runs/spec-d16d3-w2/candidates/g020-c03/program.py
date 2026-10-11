import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane data
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


def _pg_data(q):
    """PG(2,q) incidence data: m, edges, point_lines, line_points, point-index map.
    Points are 0..m-1, lines are indexed 0..m-1 (line j is the dual of point j)."""
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _improve_arc(S, s, m, pl, lp, rng, deadline, iters):
    """Plateau search: add a point, evicting at most one blocking element, keeping loads <= s."""
    S = list(S)
    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if P in S:
            continue
        cl = [0] * m
        cp = [0] * m
        for X in S:
            for L in pl[X]:
                cl[L] += 1
            for Q in lp[X]:
                cp[Q] += 1
        blockers = set()
        for L in pl[P]:
            if cl[L] >= s:
                blockers.update(X for X in S if L in pl[X])
        for Q in lp[P]:
            if cp[Q] >= s:
                blockers.update(X for X in S if Q in lp[X])
        if len(blockers) > 1:
            continue
        T = [X for X in S if X not in blockers] + [P]
        if _loads_ok(T, s, m, pl, lp):
            S = T
    return S


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S, pl, lp):
    """PG(2,q) incidence plus, per element of S, an A-vertex (joined to lines through it)
    and a B-vertex (joined to points on its line). Returns (n, edges, side)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph.
    Larger q are processed first so they are not starved by the deadline."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    for q in sorted(qs, reverse=True):
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if s >= 1 and S:
            S = _improve_arc(S, s, m, pl, lp, rng, deadline, 1500)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E, side = _arc_graph(m, edges, S, pl, lp)
        if not lib.is_valid(n, E, d, 3):
            continue
        out.append((n, E, side, m, pl, lp))
    return out


# ----------------------------------------------------------------------------
# Degree-preserving bipartite repair annealing (adds two vertices at a time).
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D, computed with bitmask balls."""
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
    """Return ops keeping max degree <= d (2-opt swap, edge add, or endpoint shift), or None."""
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


def _repair(n, adj, side0, side1, d, D, rng, deadline, max_iter):
    """Anneal until no pair is at distance > D. Returns True on success (adj updated in place)."""
    cost = _bad_pairs(n, adj, D)
    T = 1.0
    it = 0
    while cost > 0:
        if it >= max_iter or time.monotonic() > deadline:
            return False
        it += 1
        T = max(0.08, T * 0.999)
        ops = _propose(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(adj, [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)])
    return True


def _grow(n, E, side, d, D, rng, deadline, consider):
    """Repeatedly append one A and one B vertex and repair until diameter D again."""
    adj = _to_adj(n, E)
    side = list(side)
    while time.monotonic() < deadline and n + 2 <= _moore(d, D):
        adj.append(set())
        adj.append(set())
        side += [0, 1]
        n += 2
        s0 = [v for v in range(n) if side[v] == 0]
        s1 = [v for v in range(n) if side[v] == 1]
        if not _repair(n, adj, s0, s1, d, D, rng, deadline, 1500):
            break
        E2 = [(x, y) for x in range(n) for y in adj[x] if x < y]
        if not lib.is_valid(n, E2, d, D):
            break
        consider(n, E2)


# ----------------------------------------------------------------------------
# Validity-checked star add / vertex removal walk on a valid graph.
# ----------------------------------------------------------------------------

def _star_search(E0, m, pl, lp, d, D, deadline, rng):
    """Random walk over valid graphs: add a star vertex (lines through a point, or points
    on a line) using spare-degree neighbours, or delete a vertex. Returns the best (n, E)."""
    cur = list(E0)

    def count(E):
        return len({x for e in E for x in e})

    best_cnt = count(cur)
    best = list(cur)
    nxt = max(x for e in cur for x in e) + 1
    while time.monotonic() < deadline:
        deg = {}
        for u, v in cur:
            deg[u] = deg.get(u, 0) + 1
            deg[v] = deg.get(v, 0) + 1
        if rng.random() < 0.6:
            if rng.random() < 0.5:
                cand = [m + L for L in pl[rng.randrange(m)]]
            else:
                cand = list(lp[rng.randrange(m)])
            nb = [u for u in cand if deg.get(u, 0) < d]
            if len(nb) < 2:
                continue
            new = cur + [(nxt, u) for u in nb]
            nxt_new = nxt + 1
        else:
            v = rng.choice(list(deg))
            new = [e for e in cur if v not in e]
            nxt_new = nxt
        cnt = count(new)
        if cnt < best_cnt - 3:
            continue
        n_new, E_new = lib.relabel(new)
        if lib.is_valid(n_new, E_new, d, D):
            cur = new
            nxt = nxt_new
            if cnt > best_cnt:
                best_cnt = cnt
                best = list(new)
    return lib.relabel(best)


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
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

    if D >= 3:
        cands = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda c: -c[0])
        for c in cands:
            consider(c[0], c[1])

        if D == 3 and cands:
            n, E, side, m, pl, lp = cands[0]
            # Phase 1: repair-annealing growth from the best arc graph.
            _grow(n, E, side, d, D, rng, start + 0.6 * budget, consider)
            # Phase 2: star-add / delete walk from the best valid graph found so far.
            if time.monotonic() < deadline:
                n2, E2 = _star_search(best_E, m, pl, lp, d, D, deadline, rng)
                consider(n2, E2)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
