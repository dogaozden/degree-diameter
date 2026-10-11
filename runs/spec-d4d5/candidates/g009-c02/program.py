import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

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
# Degree-preserving grow-and-repair search.
#
# Invariant: every vertex keeps degree <= d and the graph stays bipartite.
# color[v] = 0 for the "A" side, 1 for the "B" side; E holds (A, B) pairs.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Ordered count of (source, target) pairs not within distance D (twice the unordered count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _colors(n, adj):
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


def _edge_list(n, adj, color):
    return [(u, v) for u in range(n) if color[u] == 0 for v in adj[u]]


def _swap(adj, E, i, j):
    """Replace A-B edges (p,q),(r,s) with (p,s),(r,q). Degrees are preserved."""
    p, q = E[i]
    r, s = E[j]
    adj[p].discard(q)
    adj[q].discard(p)
    adj[r].discard(s)
    adj[s].discard(r)
    adj[p].add(s)
    adj[s].add(p)
    adj[r].add(q)
    adj[q].add(r)
    E[i] = (p, s)
    E[j] = (r, q)


def _insert(n, adj, color, d, rng):
    """Add a new A vertex and a new B vertex, each of degree d, by splicing d disjoint edges.

    Every spliced edge (x, y) becomes (new_A, y) and (x, new_B), so existing degrees are unchanged.
    Returns the new vertex count, or None if no suitable set of d edges exists.
    """
    E = _edge_list(n, adj, color)
    if len(E) < d:
        return None
    order = list(range(len(E)))
    rng.shuffle(order)
    chosen = []
    xs, ys = set(), set()
    for i in order:
        x, y = E[i]
        if x in xs or y in ys:
            continue
        chosen.append((x, y))
        xs.add(x)
        ys.add(y)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    color.append(0)
    color.append(1)
    for x, y in chosen:
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
    return n + 2


def _anneal(n, adj, E, D, cost, rng, iters, T, deadline):
    """Metropolis walk over degree-preserving edge switches, minimizing _bad."""
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        if len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        p, q = E[i]
        r, s = E[j]
        if p == r or q == s or s in adj[p] or q in adj[r]:
            continue
        _swap(adj, E, i, j)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(adj, E, i, j)  # the inverse switch restores the previous edges
    return cost


def _search(d, D, base, deadline, rng):
    """Grow the base two vertices at a time, repairing diameter by annealing.

    Returns a list of (n, edge_list) records, each claimed valid (verified by the caller).
    """
    n0, e0 = base
    adj = [set() for _ in range(n0)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    color = _colors(n0, adj)
    n = n0
    moore = lib._moore_bound(d, D)

    records = [(n0, list(e0))]
    saved = (n, [set(s) for s in adj], list(color))

    T = 2.0
    CHUNK = 500
    STALL = 10
    stall = 0

    while time.monotonic() < deadline:
        E = _edge_list(n, adj, color)
        cost = _bad(n, adj, D)
        if cost == 0:
            records.append((n, list(E)))
            saved = (n, [set(s) for s in adj], list(color))
            if n >= moore:
                break
            nn = _insert(n, adj, color, d, rng)
            if nn is None:
                break
            n = nn
            stall = 0
            continue

        _anneal(n, adj, E, D, cost, rng, CHUNK, T, deadline)
        stall += 1
        if stall >= STALL:
            # Restart from the last valid graph with a fresh random splice.
            n, sadj, scol = saved
            adj = [set(s) for s in sadj]
            color = list(scol)
            stall = 0
    return records


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Candidate d-regular bases; keep the largest one that passes validation.
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    q = d - 1
    if D >= 3 and lib.is_prime_power(q):
        cands.append(lib.projective_plane_incidence(q))
    if D >= 4 and lib.is_prime_power(q) and q <= 4:
        cands.append(_gq_w(q))

    base = None
    for n0, e0 in cands:
        if lib.is_valid(n0, e0, d, D) and (base is None or n0 > base[0]):
            base = (n0, e0)
    if base is None:
        return lib.haar_graph(d, range(d))
    if base[0] >= lib._moore_bound(d, D):
        return base

    records = [(base[0], list(base[1]))]
    try:
        records = _search(d, D, base, deadline, rng) or records
    except Exception:
        pass  # keep whatever has been recorded so far

    # Return the largest record that passes the full validity check.
    records.sort(key=lambda t: -t[0])
    for n_r, E_r in records:
        edges = [(int(u), int(v)) for u, v in E_r]
        if lib.is_valid(n_r, edges, d, D):
            return n_r, edges

    return lib.haar_graph(d, range(d))
