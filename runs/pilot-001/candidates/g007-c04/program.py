import itertools
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _largest_pp_at_most(x, cap=None):
    """Largest prime power q with 2 <= q <= min(x, cap), or None."""
    top = x if cap is None else min(x, cap)
    for q in range(top, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (kept from the parent).
#
# A bipartite graph with spare degree can be grown without breaking its diameter.
# A new vertex v placed on side X, joined to a set S of deficient vertices on the
# opposite side, has distance at most D to every old vertex exactly when the balls
# of radius D-1 around S cover the whole graph. Existing distances can only shrink
# when a vertex is added, so validity is preserved.
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


def _extend_cover(n, edges, d, D, deadline):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]

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

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            covered = 0
            chosen = []
            pool = set(cands)
            while covered != full and len(chosen) < d and pool:
                best_s, best_g = None, 0
                for s in pool:
                    g = (ball[s] & ~covered).bit_count()
                    if g > best_g:
                        best_g, best_s = g, s
                if best_s is None:
                    break
                chosen.append(best_s)
                covered |= ball[best_s]
                pool.discard(best_s)
            if covered == full and chosen:
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


# ----------------------------------------------------------------------------
# NEW: cap-growing repair.
#
# Start from a bipartite graph that has spare degree (e.g. PG(2,q) or W(q) built
# with q small enough that degree q+1 < d). Repeatedly:
#   1. attach a new vertex to up to d deficient vertices on the opposite side;
#   2. repair: while some pair x,y is farther than D apart, add a cross edge
#      u-v with u near x, v near y (dist(x,u) + 1 + dist(v,y) <= D) using spare
#      degree. Adding edges never lengthens a path, so the repair only helps and
#      each added edge makes the pair (x,y) fine.
#   3. keep the grown graph if the repair finished, otherwise roll back.
# The result is always a valid graph for (d, D), and it is rechecked by lib.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _two_color(adj):
    n = len(adj)
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


def _reach_sets(adj, D):
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _bfs_upto(adj, src, lim):
    n = len(adj)
    dist = [-1] * n
    dist[src] = 0
    frontier = [src]
    for r in range(1, lim + 1):
        nxt = []
        for x in frontier:
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = r
                    nxt.append(y)
        if not nxt:
            break
        frontier = nxt
    return dist


def _repair_bipartite(adj, color, cap, D, rng, max_steps, deadline):
    """Add cross edges (using spare degree below cap) until diameter <= D. Returns success."""
    n = len(adj)
    full = (1 << n) - 1
    for _ in range(max_steps):
        if time.monotonic() > deadline:
            return False
        reach = _reach_sets(adj, D)
        bad = [x for x in range(n) if reach[x] != full]
        if not bad:
            return True
        x = rng.choice(bad)
        rx = reach[x]
        missing = [y for y in range(n) if not (rx >> y) & 1]
        y = rng.choice(missing)
        dx = _bfs_upto(adj, x, D)
        dy = _bfs_upto(adj, y, D)
        U = [u for u in range(n) if dx[u] >= 0 and len(adj[u]) < cap]
        V = [v for v in range(n) if dy[v] >= 0 and len(adj[v]) < cap]
        rng.shuffle(U)
        rng.shuffle(V)
        pick = None
        for u in U:
            for v in V:
                if (dx[u] + dy[v] + 1 <= D and color[u] != color[v]
                        and u != v and v not in adj[u]):
                    pick = (u, v)
                    break
            if pick is not None:
                break
        if pick is None:
            continue
        u, v = pick
        adj[u].add(v)
        adj[v].add(u)
    return False


def _grow_repair(n, edges, d, D, rng, deadline):
    """Grow a graph with spare degree by attaching vertices and repairing distances.

    Returns (n, edges) of the largest state reached; it is valid for (d, D)
    whenever the input was valid.
    """
    adj = _adj_sets(n, edges)
    color = _two_color(adj)
    best_state = (n, list(edges))
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = color[:]
        c = rng.randrange(2)
        cs = None
        for cc in (c, 1 - c):
            cand = [s for s in range(len(adj)) if color[s] == cc and len(adj[s]) < d]
            if len(cand) >= 2:
                c, cs = cc, cand
                break
        if cs is None:
            break
        k = min(d, len(cs))
        chosen = rng.sample(cs, k)
        v = len(adj)
        adj.append(set(chosen))
        color.append(1 - c)
        for s in chosen:
            adj[s].add(v)
        if _repair_bipartite(adj, color, d, D, rng, 120, deadline):
            out = [(u, w) for u in range(len(adj)) for w in adj[u] if u < w]
            best_state = (len(adj), out)
        else:
            adj, color = snap_adj, snap_color
    return best_state


# ----------------------------------------------------------------------------
# Parent search routines.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    grow_deadline = start + 0.3 * time_limit
    ext_deadline = start + 0.4 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # NEW phase: cap-growing repair from seeds with spare degree (degree < d).
    # Seeds: PG(2,q) and W(q) with q the largest prime power <= d - 2, so their
    # degree q + 1 <= d - 1 leaves room for new vertices.
    if D >= 3 and d >= 4:
        seeds = []
        q = _largest_pp_at_most(d - 2)
        if q is not None:
            seeds.append(lib.projective_plane_incidence(q))
            if D >= 4:
                qg = _largest_pp_at_most(d - 2, cap=7)
                if qg is not None:
                    seeds.append(_gq_w(qg))
        for i, (sn, se) in enumerate(seeds):
            now = time.monotonic()
            share = (grow_deadline - now) / (len(seeds) - i)
            if share <= 0:
                break
            res = _grow_repair(sn, se, d, D, rng, now + share)
            consider(res[0], res[1])

    # D >= 3: projective plane with largest prime power q <= d - 1
    # (diameter 3 <= D), then grown by cover-based extension into its spare degree.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _extend_cover(pg[0], pg[1], d, D, ext_deadline)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) with q + 1 <= d (diameter 4 <= D),
    # also grown by cover-based extension.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _extend_cover(gq[0], gq[1], d, D, ext_deadline)
            consider(n2, e2)

    # Mixed search: Haar graphs with growing modulus, and random-base voltage lifts.
    base_sizes = [1, 2, 3, 4, 5, 6]
    ladder = {k: 2 for k in base_sizes}
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        if rng.random() < 0.35 and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
