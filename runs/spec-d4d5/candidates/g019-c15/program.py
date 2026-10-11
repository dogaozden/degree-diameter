import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seed families (valid for diameter 3 and 4).
# ----------------------------------------------------------------------------

def _largest_pp(hi, lo=2):
    """Largest prime power q with lo <= q <= hi, or None."""
    for q in range(hi, lo - 1, -1):
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Unstructured repair search: grow a valid bipartite graph one vertex pair at a
# time, attaching the new vertices, then anneal edge switches to minimise the
# number of pairs at distance > D. Degrees never exceed d.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bip_colors(n, adj):
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    total = 0
    for r in reach:
        total += n - r.bit_count()
    return total // 2


def _attach(adj, x, pool, d, rng, count):
    """Give new vertex x up to `count` further neighbours from pool, stealing a slot if needed."""
    cands = rng.sample(pool, min(len(pool), 3 * count + 3))
    added = 0
    for t in cands:
        if added >= count:
            break
        if t in adj[x]:
            continue
        if len(adj[t]) >= d:
            u = rng.choice(tuple(adj[t]))
            adj[u].discard(t)
            adj[t].discard(u)
        adj[x].add(t)
        adj[t].add(x)
        added += 1


def _anneal(n, adj, Lv, Rv, d, D, rng, deadline, iters):
    """Simulated annealing on edge switches and edge additions. Returns final cost (0 = valid)."""
    cost = _bad_pairs(n, adj, D)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if rng.random() < 0.2:
            u = rng.choice(Lv)
            v = rng.choice(Rv)
            if v in adj[u] or len(adj[u]) >= d or len(adj[v]) >= d:
                continue
            adj[u].add(v)
            adj[v].add(u)
            c2 = _bad_pairs(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[u].discard(v)
                adj[v].discard(u)
        else:
            u1 = rng.choice(Lv)
            u2 = rng.choice(Lv)
            if u1 == u2 or not adj[u1] or not adj[u2]:
                continue
            v1 = rng.choice(tuple(adj[u1]))
            v2 = rng.choice(tuple(adj[u2]))
            if v2 in adj[u1] or v1 in adj[u2]:
                continue
            adj[u1].discard(v1)
            adj[v1].discard(u1)
            adj[u2].discard(v2)
            adj[v2].discard(u2)
            adj[u1].add(v2)
            adj[v2].add(u1)
            adj[u2].add(v1)
            adj[v1].add(u2)
            c2 = _bad_pairs(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[u1].discard(v2)
                adj[v2].discard(u1)
                adj[u2].discard(v1)
                adj[v1].discard(u2)
                adj[u1].add(v1)
                adj[v1].add(u1)
                adj[u2].add(v2)
                adj[v2].add(u2)
    return cost


def _grow(seed_n, seed_edges, d, D, deadline, rng, bound, consider):
    """Repeatedly add vertex pairs and repair with annealing; report every valid success."""
    n = seed_n
    adj = _to_adj(n, seed_edges)
    color = _bip_colors(n, adj)
    Lv = [v for v in range(n) if color[v] == 0]
    Rv = [v for v in range(n) if color[v] == 1]
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        step = max(1, len(Lv) // 40)
        while step > 1 and n + 2 * step > bound:
            step -= 1
        if n + 2 * step > bound:
            break
        adj2 = [set(s) for s in adj]
        Lv2, Rv2 = list(Lv), list(Rv)
        n2 = n
        for _ in range(step):
            x, y = n2, n2 + 1
            n2 += 2
            adj2.append(set())
            adj2.append(set())
            Lv2.append(x)
            Rv2.append(y)
            adj2[x].add(y)
            adj2[y].add(x)
            _attach(adj2, x, Rv2, d, rng, d - 1)
            _attach(adj2, y, Lv2, d, rng, d - 1)
        cost = _anneal(n2, adj2, Lv2, Rv2, d, D, rng, deadline, 500)
        if cost == 0:
            edges = [(u, v) for u in range(n2) for v in adj2[u] if u < v]
            consider(n2, edges)
            n, adj, Lv, Rv = n2, adj2, Lv2, Rv2
            fails = 0
        else:
            fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Structured seeds: projective plane (D >= 3) and generalized quadrangle (D >= 4).
    if D >= 3:
        q = _largest_pp(d - 1)
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
    if D >= 4:
        q = _largest_pp(min(d - 1, 9))
        if q is not None:
            n, e = _gq_w(q)
            consider(n, e)

    # Unstructured grow-and-repair search from the best valid graph found so far.
    bound = lib._moore_bound(d, D)
    if d >= 2 and best_n + 2 <= bound:
        _grow(best_n, best_e, d, D, deadline, rng, bound, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
