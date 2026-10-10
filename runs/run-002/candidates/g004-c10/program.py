import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe structured starts for D = 3 and D = 4 (projective plane and generalized
# quadrangle), extended greedily. Unchanged in spirit from the parent.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    color = _bipartition(n, adj)

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
    """Alternate edge saturation and cover extension until no vertex can be added."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline)
        if n2 == cur_n:
            break
        cur_n, cur_e = n2, e2
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main bold family: voltage lifts over NON-cyclic groups (semidirect products
# Z_m x| Z_k2), with a fast diameter oracle.
#
# Key fact: the lift with edges (u, x) -- (v, x*g) is invariant under left
# multiplication by any group element. So every vertex of block u is equivalent
# to (u, e). The lift has diameter <= D iff a BFS of depth D from each of the
# 2k representatives (u, e) reaches every vertex. That is 2k BFS runs instead
# of an all-pairs bitmask computation, which makes the hill-climb much faster.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a semidirect product Z_m x| Z_k2 with order >= G, or None."""
    for g in range(G, G + 25):
        divs = [k2 for k2 in range(1, 13) if g % k2 == 0 and g // k2 >= 2]
        if not divs:
            continue
        rng.shuffle(divs)
        for k2 in divs[:4]:
            m = g // k2
            if k2 == 1:
                r = 1
            else:
                cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                         if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
                if not cands:
                    continue
                r = rng.choice(cands)
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            return order, mul
    return None


def _cost(k, order, darts, mul, D):
    """Total number of (representative, vertex) pairs at distance > D. Zero iff diameter <= D."""
    n = 2 * k * order
    edges = set()
    for u, v, g in darts:
        for x in range(order):
            edges.add((u * order + x, v * order + mul(x, g)))
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)

    total = 0
    for u in range(2 * k):
        src = u * order  # identity element is code 0 in both cyclic and semidirect codings
        dist = [-1] * n
        dist[src] = 0
        frontier = [src]
        seen = 1
        for depth in range(1, D + 1):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if dist[b] < 0:
                        dist[b] = depth
                        nxt.append(b)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - seen
    return total


def _lift_search(d, D, k, order, mul, rng, iters, deadline):
    """Random d-regular base with k + k vertices; hill-climb voltages. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, k + p[i], rng.randrange(order)])

    c = _cost(k, order, darts, mul, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = rng.randrange(order)
        c2 = _cost(k, order, darts, mul, D)
        if c2 <= c or rng.random() < 0.03:
            c = c2
        else:
            darts[j][2] = old
    if c == 0:
        return [tuple(x) for x in darts]
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.75 * time_limit, time_limit - 4.0))
    ext_deadline = start + 0.25 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, bipartite with diameter 2 (valid for D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    try:
        # Structured starts.
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng)
                consider(n2, e2)

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
                consider(n2, e2)

        # Main search: fast non-cyclic group lifts.
        base_sizes = [1, 2, 3, 4, 5, 6]
        iters = 300
        while time.monotonic() < deadline:
            k = rng.choice(base_sizes)
            G = max(best_n // (2 * k) + 1, 2) + rng.randint(0, 3)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            darts = _lift_search(d, D, k, order, mul, rng, iters, deadline)
            if darts is not None:
                n, e = lib.group_lift(2 * k, darts, order, mul)
                consider(n, e)
    except Exception:
        # Any unexpected failure in the search falls through to the best valid graph so far.
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
