"""Cover-growth with simulated-annealing cover search and iterated local search.

Approach (different from the twin-packing pipeline):
  * Base graphs: PG(2, q) for D = 3, the generalized quadrangle W(q) for D = 4,
    and K_{d,d} otherwise.
  * Growth: a new vertex on one side is joined to d opposite-side vertices with
    spare degree whose radius-(D-1) balls cover the whole graph. The cover is
    found by greedy initialisation followed by simulated annealing on the
    number of uncovered vertices. Adding a vertex this way keeps the diameter
    at most D, since existing distances can only shrink.
  * Search: iterated local search. Random vertices are deleted, the graph is
    repaired and regrown, and accepted when it does not shrink. Every stored
    graph is verified with lib.is_valid.
  * Fallback: K_{d,d}, which is always valid for D >= 2.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs
# ----------------------------------------------------------------------------

def _pg(q):
    return lib.projective_plane_incidence(q)


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


# ----------------------------------------------------------------------------
# Graph utilities
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
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
    """Bitmask of all vertices within distance r of each vertex."""
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


def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


# ----------------------------------------------------------------------------
# Cover search (simulated annealing)
# ----------------------------------------------------------------------------

def _uncovered(S, ball, full):
    c = 0
    for s in S:
        c |= ball[s]
    return (full & ~c).bit_count()


def _cover_sa(cands, ball, full, k, rng, iters, randomize):
    """Find k candidates whose balls cover `full`; returns the list or None."""
    k = min(k, len(cands))
    if k <= 0:
        return None
    chosen = []
    in_set = set()
    covered = 0
    for _ in range(k):
        best_g = -1.0
        best_s = None
        for s in cands:
            if s in in_set:
                continue
            g = (ball[s] & ~covered).bit_count()
            if randomize:
                g += rng.random()
            if g > best_g:
                best_g = g
                best_s = s
        chosen.append(best_s)
        in_set.add(best_s)
        covered |= ball[best_s]

    cur = _uncovered(chosen, ball, full)
    best_val = cur
    best_S = list(chosen)
    cand_list = list(cands)
    for it in range(iters):
        if best_val == 0:
            break
        T = 1.5 * (1.0 - it / iters) + 0.05
        i = rng.randrange(k)
        new = cand_list[rng.randrange(len(cand_list))]
        if new in in_set:
            continue
        old = chosen[i]
        chosen[i] = new
        val = _uncovered(chosen, ball, full)
        delta = val - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            in_set.discard(old)
            in_set.add(new)
            cur = val
            if cur < best_val:
                best_val = cur
                best_S = list(chosen)
        else:
            chosen[i] = old
    return best_S if best_val == 0 else None


# ----------------------------------------------------------------------------
# Growth and saturation (both preserve diameter <= D and bipartiteness)
# ----------------------------------------------------------------------------

def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add a cover vertex on either side while one exists."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    while time.monotonic() < deadline:
        ball = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for c in sides:
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(4):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover_sa(cands, ball, full, d, rng, 400, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                placed = True
                break
        if not placed:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Add random edges between opposite-side vertices that still have spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Structured base graph.
    base = None
    if D == 3:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                base = _pg(q)
                break
    elif D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                base = _gq_w(q)
                break

    if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
        best = base

    # Initial growth from the best valid start.
    n, e = _grow(best[0], best[1], d, D, rng, deadline)
    e = _saturate(n, e, d, rng)
    if n > best[0] and lib.is_valid(n, e, d, D):
        best = (n, e)

    # Iterated local search: delete a few vertices, repair, regrow.
    while time.monotonic() < deadline:
        n, e = best[0], list(best[1])
        for _ in range(rng.choice([1, 1, 2, 2, 3])):
            if n <= 2:
                break
            x = rng.randrange(n)
            n, e = _remove_vertex(n, e, x)
        if n <= 1:
            continue
        if not lib.within_diameter(n, e, D):
            e = _saturate(n, e, d, rng)
            if not lib.within_diameter(n, e, D):
                continue
        n, e = _grow(n, e, d, D, rng, deadline)
        e = _saturate(n, e, d, rng)
        if n >= best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))
