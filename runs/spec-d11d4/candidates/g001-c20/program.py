import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (diameter 3) and generalized quadrangle W(q) (diameter 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colouring(n, adj):
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


def _ball_masks(n, adj, r):
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-colour vertices in random order.

    Adding edges never increases a distance, so diameter, bipartiteness and
    degree bound are all preserved.
    """
    edges = list(edges)
    adj = _adj_lists(n, edges)
    deg = [len(a) for a in adj]
    color = _colouring(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


# ----------------------------------------------------------------------------
# New idea: paired-gadget growth.
#
# Add two new adjacent vertices a (colour a_side) and b (colour 1 - a_side) at
# once. a takes neighbours on the opposite side (up to d-1 of them), and b does
# likewise, so each has degree <= d with the a-b edge. Diameter stays <= D when
# every old vertex u satisfies:
#   d(a,u) <= D via a's neighbour x  :  u in ball_{D-1}(x), or
#                via b's neighbour y :  u in ball_{D-2}(y)
#   and symmetrically for b.
# Each candidate x attached to a therefore contributes ball_{D-1}(x) to a's
# cover and ball_{D-2}(x) to b's cover (and vice versa). Both covers are built
# greedily at once, so one candidate helps both new vertices. The pair gives
# two vertices for the price of spare degree that a single cover vertex would
# need, which lets the spare capacity of a near-saturated base go further.
# ----------------------------------------------------------------------------

def _try_pair(n, B_own, B_via, deg, color, a_side, d, full, rng):
    """Greedy cover for a new pair. Returns (a_side, na, nb) or None."""
    pa = [v for v in range(n) if color[v] == 1 - a_side and deg[v] < d]
    pb = [v for v in range(n) if color[v] == a_side and deg[v] < d]
    rng.shuffle(pa)
    rng.shuffle(pb)
    cov_a = 0
    cov_b = 0
    na, nb = [], []
    cap = d - 1
    while cov_a != full or cov_b != full:
        best = None
        bg = 0
        if len(na) < cap:
            for x in pa:
                g = (B_own[x] & ~cov_a).bit_count() + (B_via[x] & ~cov_b).bit_count()
                if g > bg:
                    bg, best = g, (0, x)
        if len(nb) < cap:
            for y in pb:
                g = (B_own[y] & ~cov_b).bit_count() + (B_via[y] & ~cov_a).bit_count()
                if g > bg:
                    bg, best = g, (1, y)
        if best is None:
            return None
        side, x = best
        if side == 0:
            na.append(x)
            pa.remove(x)
            cov_a |= B_own[x]
            cov_b |= B_via[x]
        else:
            nb.append(x)
            pb.remove(x)
            cov_b |= B_own[x]
            cov_a |= B_via[x]
    return a_side, na, nb


def _link(adj, deg, edges, u, v):
    edges.append((u, v))
    adj[u].append(v)
    adj[v].append(u)
    deg[u] += 1
    deg[v] += 1


def _pair_grow(n, edges, d, D, deadline, rng, tries=4):
    """Repeatedly add paired gadgets while a valid cover exists. Requires D >= 3."""
    edges = list(edges)
    adj = _adj_lists(n, edges)
    deg = [len(a) for a in adj]
    color = _colouring(n, adj)
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        B_own = _ball_masks(n, adj, D - 1)
        B_via = _ball_masks(n, adj, D - 2)
        found = None
        for _ in range(tries):
            if time.monotonic() >= deadline:
                break
            a_side = rng.randrange(2)
            res = _try_pair(n, B_own, B_via, deg, color, a_side, d, full, rng)
            if res is not None:
                found = res
                break
        if found is None:
            break
        a_side, na, nb = found
        a, b = n, n + 1
        n += 2
        adj.append([])
        adj.append([])
        deg.append(0)
        deg.append(0)
        color.append(a_side)
        color.append(1 - a_side)
        _link(adj, deg, edges, a, b)
        for x in na:
            _link(adj, deg, edges, a, x)
        for y in nb:
            _link(adj, deg, edges, b, y)
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5 * time_limit, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D < 3:
        return best_n, best_e

    # Choose the base: generalized quadrangle for D >= 4, projective plane otherwise.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None:
        base = _best_pg(d)
    if base is None:
        return best_n, best_e

    bn, be = base
    consider(bn, be)

    # Restarts of paired-gadget growth, alternating between plain and
    # pre-saturated starting points, until the deadline.
    while time.monotonic() < deadline:
        start_edges = be
        if rng.random() < 0.5:
            start_edges = _saturate(bn, be, d, rng)
        n2, e2 = _pair_grow(bn, start_edges, d, D, deadline, rng)
        e3 = _saturate(n2, e2, d, rng)
        consider(n2, e3)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
