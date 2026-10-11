import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _largest_pp(limit):
    """Largest prime power q with 2 <= q <= limit, or None."""
    for q in range(limit, 1, -1):
        if lib.is_prime_power(q):
            return q
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
# Mutable graph state: adjacency sets plus a fixed 2-colouring.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(n, adj, color, d, rng):
    """Greedily add edges between opposite-side vertices with spare degree.
    Adding edges never increases distances, so this is always safe."""
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        if len(adj[a]) >= d:
            continue
        for b in B:
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                if len(adj[a]) >= d:
                    break


def _attach(n, adj, color, d, c, rng):
    """Append a vertex on side c. It joins up to d opposite-side vertices with spare
    degree; if there are not enough, it steals an edge from a full opposite vertex.
    Returns the new vertex count."""
    o = 1 - c
    v = n
    adj.append(set())
    color.append(c)
    cands = [y for y in range(n) if color[y] == o and len(adj[y]) < d]
    rng.shuffle(cands)
    chosen = cands[:d]
    for y in chosen:
        adj[v].add(y)
        adj[y].add(v)
    need = d - len(chosen)
    if need > 0:
        full = [y for y in range(n) if color[y] == o and len(adj[y]) >= d]
        rng.shuffle(full)
        for y in full:
            if need <= 0:
                break
            z = rng.choice(tuple(adj[y]))  # z lies on side c, so z != v
            adj[y].discard(z)
            adj[z].discard(y)
            adj[y].add(v)
            adj[v].add(y)
            need -= 1
    return n + 1


def _anneal(n, adj, color, D, rng, deadline, iters, T0):
    """Simulated annealing over degree-preserving bipartite edge switches,
    minimising the number of bad pairs. Returns the final cost (0 = valid diameter)."""
    cost = _bad(n, adj, D)
    if cost == 0:
        return 0
    sideA = [v for v in range(n) if color[v] == 0 and adj[v]]
    if len(sideA) < 2:
        return cost
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (0.02 ** (it / iters))
        a = rng.choice(sideA)
        c = rng.choice(sideA)
        if a == c:
            continue
        b = rng.choice(tuple(adj[a]))
        e = rng.choice(tuple(adj[c]))
        if b == e or e in adj[a] or b in adj[c]:
            continue
        # Switch (a,b),(c,e) -> (a,e),(c,b). Degrees are unchanged.
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cost


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 3.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Base graph: projective plane for D = 3, generalized quadrangle for D = 4.
    base = None
    try:
        if D == 3:
            q = _largest_pp(d - 1)
            if q is not None:
                base = lib.projective_plane_incidence(q)
        elif D == 4:
            q = _largest_pp(d - 1)
            if q is not None:
                base = _gq_w(q)
    except Exception:
        base = None

    if base is not None:
        consider(base[0], base[1])

    # Growth: add one vertex at a time, repair the diameter by annealing,
    # and roll back when the repair fails.
    try:
        if base is not None and best[0] >= 2:
            n = base[0]
            adj = _adj_sets(n, base[1])
            color = _bipartition(n, adj)
            _fill(n, adj, color, d, rng)
            cur_n = n
            cur_adj = adj
            cur_color = color

            while time.monotonic() < deadline:
                adj_w = [set(s) for s in cur_adj]
                col_w = list(cur_color)
                n1 = _attach(cur_n, adj_w, col_w, d, rng.randrange(2), rng)
                _fill(n1, adj_w, col_w, d, rng)
                cap = min(deadline, time.monotonic() + 5.0)
                cost = _anneal(n1, adj_w, col_w, D, rng, cap, 4000, 1.0)
                if cost == 0:
                    cur_n, cur_adj, cur_color = n1, adj_w, col_w
                    if n1 > best[0]:
                        consider(n1, _to_edges(n1, adj_w))
                # Otherwise the working copy is discarded and cur_* stays intact.
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
