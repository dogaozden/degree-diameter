import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
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


# ----------------------------------------------------------------------------
# Twin augmentation: a twin of x shares x's neighbourhood. This keeps bipartiteness
# and diameter, and uses one unit of slack on every neighbour of x.
# ----------------------------------------------------------------------------

def _twin_packing(adj, d, rng, deadline):
    n = len(adj)
    slack = [d - len(a) for a in adj]
    cand = [x for x in range(n) if adj[x]]
    inset = [False] * n
    load = [0] * n

    def ok(x):
        return all(load[w] < slack[w] for w in adj[x])

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and ok(x):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        if chosen:
            for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
                drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(inset)
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    chosen = _twin_packing([list(a) for a in adj], d, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Fixed-order annealing with vertex growth.
#
# The graph is kept bipartite (color array). Each growth step adds one vertex per
# side, fills them greedily from spare degree, then anneals on the number of
# bad pairs (distance > D) with degree-safe moves:
#   switch   : 2-switch on two edges (keeps all degrees)
#   add      : join a deficient opposite-side pair
#   transfer : a deficient vertex takes a neighbour from another vertex
# A step is accepted only if the annealing reaches zero bad pairs.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
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


def _random_edge(n, adj, color, rng):
    v = rng.randrange(n)
    if not adj[v]:
        return None
    u = rng.choice(tuple(adj[v]))
    return (v, u) if color[v] == 0 else (u, v)


def _propose(n, adj, color, d, rng):
    r = rng.random()
    if r < 0.5:
        e1 = _random_edge(n, adj, color, rng)
        e2 = _random_edge(n, adj, color, rng)
        if e1 is None or e2 is None:
            return None
        a, b = e1
        c, e = e2
        if a == c or b == e or e in adj[a] or b in adj[c]:
            return None
        return [('d', a, b), ('d', c, e), ('a', a, e), ('a', c, b)]
    if r < 0.75:
        d0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if not d0 or not d1:
            return None
        x = rng.choice(d0)
        y = rng.choice(d1)
        if y in adj[x]:
            return None
        return [('a', x, y)]
    x = rng.randrange(n)
    if len(adj[x]) >= d:
        return None
    y = rng.randrange(n)
    if color[y] == color[x] or not adj[y] or x in adj[y]:
        return None
    z = rng.choice(tuple(adj[y]))
    return [('d', z, y), ('a', x, y)]


def _apply(adj, ops):
    for t, x, y in ops:
        if t == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _undo(adj, ops):
    for t, x, y in reversed(ops):
        if t == 'a':
            adj[x].discard(y)
            adj[y].discard(x)
        else:
            adj[x].add(y)
            adj[y].add(x)


def _anneal(n, adj, color, d, D, deadline, rng):
    cur = _bad_count(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = 1.5 * (0.01 ** ((now - t0) / span))
        ops = _propose(n, adj, color, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        new = _bad_count(n, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            _undo(adj, ops)
    return True


def _fill_new(N, adj, color, d, new_ids, rng):
    for v in new_ids:
        cand = [w for w in range(N)
                if color[w] != color[v] and w != v and len(adj[w]) < d and w not in adj[v]]
        rng.shuffle(cand)
        for w in cand:
            if len(adj[v]) >= d:
                break
            if len(adj[w]) < d:
                adj[v].add(w)
                adj[w].add(v)


def _state(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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
    return adj, color


def _to_edges(n, adj, color):
    return n, [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Choose a structured base.
    if D == 3:
        base = _best_pg(d)
        if base is None:
            base = best
        else:
            consider(base[0], base[1])
    else:
        q = next((q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)), None)
        if q is None:
            base = best
        else:
            base = _gq_w(q)
            consider(base[0], base[1])

    # Twin augmentation of the base (uses a share of the budget).
    tn, te = _twin_augment(base[0], base[1], d, rng,
                           start + 0.3 * (deadline - start))
    consider(tn, te)

    # Growth by vertex insertion + annealing, starting from the best valid graph.
    adj, color = _state(best_n, best[1])
    n = best_n
    fails = 0
    while fails < 4:
        now = time.monotonic()
        if now >= deadline - 0.2:
            break
        rem = deadline - now
        slice_end = now + max(0.5, rem * 0.5)

        cadj = [set(s) for s in adj] + [set(), set()]
        ccol = color + [0, 1]
        N = n + 2
        _fill_new(N, cadj, ccol, d, [n, n + 1], rng)
        if _anneal(N, cadj, ccol, d, D, slice_end, rng):
            adj, color, n = cadj, ccol, N
            consider(*_to_edges(n, adj, color))
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
