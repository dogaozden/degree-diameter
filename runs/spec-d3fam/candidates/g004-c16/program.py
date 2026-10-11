import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generic helpers on bipartite graphs.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS). Zero means valid diameter."""
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


# ----------------------------------------------------------------------------
# NEW: pair insertion with degree-preserving annealing (diameter 3 records).
#
# A new point x and a new line y are added. Each new vertex needs d neighbours
# on the opposite side. Spare slots are used first; the rest come from a
# matching of existing edges (P_i, L_i) that is deleted, so P_i gets y and
# L_i gets x. The degrees of old vertices stay at most d. The result is then
# repaired with double-edge swaps (which keep every degree fixed), minimizing
# the number of pairs at distance > D. A zero cost gives a valid graph two
# vertices larger than the base.
# ----------------------------------------------------------------------------

def _insert_pair(n, adj, color, d, rng):
    """Add one point and one line to a bipartite graph by deleting a matching; returns (n+2, adj, color) or None."""
    free1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    free0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    x_nbrs = free1[:d]
    y_nbrs = free0[:d]
    need_x = d - len(x_nbrs)
    need_y = d - len(y_nbrs)
    r = max(need_x, need_y)

    edges = [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]
    rng.shuffle(edges)
    used = set()
    match = []
    for a, b in edges:
        if len(match) >= r:
            break
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        match.append((a, b))
    if len(match) < r:
        return None

    new_adj = [set(s) for s in adj] + [set(), set()]
    for a, b in match:
        new_adj[a].discard(b)
        new_adj[b].discard(a)
    x, y = n, n + 1
    xs = list(x_nbrs)
    ys = list(y_nbrs)
    for i, (a, b) in enumerate(match):
        if i < need_x:
            xs.append(b)
        if i < need_y:
            ys.append(a)
    for v in xs:
        new_adj[x].add(v)
        new_adj[v].add(x)
    for v in ys:
        new_adj[y].add(v)
        new_adj[v].add(y)
    return n + 2, new_adj, color + [0, 1]


def _pair_step(n, adj, d, D, deadline, rng):
    """Insert one pair and anneal with degree-preserving double-edge swaps; return (n2, adj2) on success."""
    color = _bipartition(n, adj)
    ins = _insert_pair(n, adj, color, d, rng)
    if ins is None:
        return None
    n2, adj2, col2 = ins
    E = [(a, b) for a in range(n2) if col2[a] == 0 for b in adj2[a]]
    if not E:
        return None
    S = set(E)
    cost = _bad(n2, adj2, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.2
    it = 0
    while cost > 0:
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        it += 1
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in S or (c, b) in S:
            continue
        # Double-edge swap: (a,b),(c,e) -> (a,e),(c,b). Degrees are unchanged.
        adj2[a].discard(b)
        adj2[b].discard(a)
        adj2[c].discard(e)
        adj2[e].discard(c)
        adj2[a].add(e)
        adj2[e].add(a)
        adj2[c].add(b)
        adj2[b].add(c)
        new_cost = _bad(n2, adj2, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            S.discard((a, b))
            S.discard((c, e))
            S.add((a, e))
            S.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj2[a].discard(e)
            adj2[e].discard(a)
            adj2[c].discard(b)
            adj2[b].discard(c)
            adj2[a].add(b)
            adj2[b].add(a)
            adj2[c].add(e)
            adj2[e].add(c)
    if cost == 0:
        return n2, adj2
    return None


def _pair_ladder(n, edges, d, D, deadline, rng):
    """Repeatedly insert pairs while annealing succeeds; return the largest valid (n, edges) reached."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    cur_n = n
    best = (n, list(edges))
    while time.monotonic() < deadline:
        step = _pair_step(cur_n, adj, d, D, deadline, rng)
        if step is None:
            break
        cur_n, adj = step
        best = (cur_n, [(a, b) for a in range(cur_n) for b in adj[a] if a < b])
    return best


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth, used for D >= 4).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph is d-regular, diameter 3.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        # New: grow the best base by pair insertion with degree-preserving annealing.
        if best_n > 2 * d:
            n2, e2 = _pair_ladder(best_n, best[1], d, D, deadline, rng)
            consider(n2, e2)
        return best

    # D >= 4 (and D == 2 falls through with only the K_{d,d} fallback).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.5 * time_limit, rng)
            consider(n2, e2)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.7 * time_limit, rng)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
