import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
#   W(q): point-line incidence graph of the generalized quadrangle W(q).
#         Degree q+1, order 2(q+1)(q^2+1), diameter 4.
#   PG(2,q): projective plane incidence, degree q+1, diameter 3.
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
# New construction: Z_m voltage lifts of a base graph of diameter D-1 (or less).
# The base W(d-1) has diameter 4; a lift that keeps diameter <= D gives a
# larger graph with the same degree and bipartition. Voltages on a spanning
# tree are gauged to 0, and the remaining voltages are annealed.
# Cost = number of ordered vertex pairs farther apart than D, computed with
# bitmask ball expansion.
# ----------------------------------------------------------------------------

def _spanning_tree_mask(n0, E0):
    adj = [[] for _ in range(n0)]
    for i, (u, v) in enumerate(E0):
        adj[u].append((v, i))
        adj[v].append((u, i))
    seen = [False] * n0
    tree = [False] * len(E0)
    seen[0] = True
    stack = [0]
    while stack:
        u = stack.pop()
        for v, i in adj[u]:
            if not seen[v]:
                seen[v] = True
                tree[i] = True
                stack.append(v)
    return tree


def _lift_adj(n0, E0, volt, m):
    N = n0 * m
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(E0, volt):
        for g in range(m):
            x = u * m + g
            y = v * m + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return N, adj


def _cost(N, adj, D):
    """Number of ordered vertex pairs at distance more than D (0 means valid)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal(n0, E0, tree, m, D, rng, deadline):
    """Simulated annealing over non-tree voltages in Z_m. Returns voltages or None."""
    free = [i for i, t in enumerate(tree) if not t]
    volt = [0] * len(E0)
    for i in free:
        volt[i] = rng.randrange(m)
    N, adj = _lift_adj(n0, E0, volt, m)
    cur = _cost(N, adj, D)
    if not free:
        return volt if cur == 0 else None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.02 * cur)
    T_end = 0.3
    while cur > 0 and time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T0 * (T_end / T0) ** frac
        i = rng.choice(free)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        N2, adj2 = _lift_adj(n0, E0, volt, m)
        c2 = _cost(N2, adj2, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            volt[i] = old
    return volt if cur == 0 else None


def _lift_edges(E0, volt, m):
    E = []
    for (u, v), a in zip(E0, volt):
        for g in range(m):
            E.append((u * m + g, v * m + (g + a) % m))
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    q = d - 1

    if D == 3:
        for qq in range(q, 1, -1):
            if lib.is_prime_power(qq):
                consider(*lib.projective_plane_incidence(qq))
                break
        return _finish(best, d, D)

    # D >= 4: base W(d-1) when d-1 is a small prime power (diameter 4 <= D).
    base = None
    if q >= 2 and q <= 7 and lib.is_prime_power(q):
        base = _gq_w(q)
        consider(base[0], base[1])

    if base is not None and D >= 4:
        n0, E0 = base
        tree = _spanning_tree_mask(n0, E0)
        # m = 2 first (secures a valid graph quickly), then m = 3 with the rest.
        plan = ((2, start + 0.3 * budget), (3, deadline))
        for m, end in plan:
            if n0 * m > moore:
                continue
            if time.monotonic() >= min(end, deadline):
                continue
            volt = _anneal(n0, E0, tree, m, D, rng, min(end, deadline))
            if volt is not None:
                consider(n0 * m, _lift_edges(E0, volt, m))

    return _finish(best, d, D)


def _finish(best, d, D):
    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
