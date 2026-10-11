import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes and generalized quadrangles.
# Each base is a bipartite graph with diameter <= 4 whose voltage lifts
# (cyclic Z_M, one fibre of M copies per base vertex) are searched for
# diameter <= D.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _tree_edges(nb, E):
    """Indices of a BFS spanning tree of the base graph, or None if it is disconnected."""
    adj = [[] for _ in range(nb)]
    for idx, (u, v) in enumerate(E):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * nb
    seen[0] = True
    stack = [0]
    tree = set()
    while stack:
        u = stack.pop()
        for v, idx in adj[u]:
            if not seen[v]:
                seen[v] = True
                tree.add(idx)
                stack.append(v)
    return tree if all(seen) else None


# ----------------------------------------------------------------------------
# Cyclic voltage lifts of a base bipartite graph, annealed on voltages.
# Voltages on a spanning tree are fixed to 0 (gauge freedom), so only the
# remaining edges are searched.
# Cost = sum over lifted vertices of the number of vertices NOT within D.
# Zero cost means the lift has diameter <= D.
# ----------------------------------------------------------------------------

def _lift_adj(nb, E, volt, M):
    N = nb * M
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(E, volt):
        ub = u * M
        vb = v * M
        for g in range(M):
            x = ub + g
            y = vb + (g + a) % M
            adj[x].append(y)
            adj[y].append(x)
    return N, adj


def _lift_cost(N, adj, D):
    """Bitset ball growth: total number of ordered pairs at distance > D (0 iff diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _lift_edges(nb, E, volt, M):
    edges = []
    for (u, v), a in zip(E, volt):
        for g in range(M):
            edges.append((u * M + g, v * M + (g + a) % M))
    return nb * M, edges


def _anneal_slice(t, D, deadline):
    """Anneal one task until cost 0 or the deadline. Returns True if a valid lift was found."""
    if not t['free']:
        return False
    rng = t['rng']
    volt = t['volt']
    free = t['free']
    M = t['M']
    nb = t['nb']
    E = t['E']
    cost = t['cost']
    T = t['T']
    while cost > 0 and time.monotonic() < deadline:
        i = free[rng.randrange(len(free))]
        old = volt[i]
        new = rng.randrange(M - 1)
        if new >= old:
            new += 1
        volt[i] = new
        N, adj = _lift_adj(nb, E, volt, M)
        c2 = _lift_cost(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            volt[i] = old
        T = max(0.25, T * 0.998)
    t['cost'] = cost
    t['T'] = T
    return cost == 0


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} meets the Moore bound 2d

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = []
    pg = _best_pg(d)
    if pg is not None:
        bases.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)

    base_data = []
    for nb, E in bases:
        consider(nb, E)
        if nb < 2:
            continue
        tree = _tree_edges(nb, E)
        if tree is not None:
            base_data.append((nb, E, tree))

    # Lift specifications (lift order, base index, Z_M order), sorted ascending.
    specs = []
    for bi, (nb, E, _) in enumerate(base_data):
        top = min(moore // nb, 3000 // nb, 40)
        for M in range(2, top + 1):
            specs.append((nb * M, bi, M))
    specs.sort()

    tasks = {}
    done = set()

    def activate(si):
        if si not in tasks:
            _, bi, M = specs[si]
            nb, E, tree = base_data[bi]
            rng = random.Random(seed * 1000003 + si * 7919 + 17)
            free = [i for i in range(len(E)) if i not in tree]
            volt = [0] * len(E)
            for i in free:
                volt[i] = rng.randrange(M)
            N, adj = _lift_adj(nb, E, volt, M)
            tasks[si] = {
                'nb': nb, 'E': E, 'M': M, 'free': free, 'volt': volt,
                'cost': _lift_cost(N, adj, D), 'T': 3.0, 'rng': rng,
            }
        return tasks[si]

    # Round-robin over lifts strictly larger than the current best, in ascending order.
    while time.monotonic() < deadline and best[0] < moore and specs:
        active = [si for si, (n_lift, _, _) in enumerate(specs)
                  if n_lift > best[0] and si not in done]
        if not active:
            break
        for si in active:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                break
            t = activate(si)
            if not t['free']:
                done.add(si)
                continue
            slice_t = min(remaining, max(0.3, remaining / (1.5 * len(active))))
            ok = _anneal_slice(t, D, now + slice_t)
            if ok:
                n, e = _lift_edges(t['nb'], t['E'], t['volt'], t['M'])
                consider(n, e)
                done.add(si)
                break  # best changed: recompute the active list

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
