import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Voltage lifts of projective-plane incidence graphs over Z_m.
#
# Base: incidence graph of PG(2, q), which is (q+1)-regular, bipartite and has
# diameter 3. A lift with voltages in Z_m has nb*m vertices and keeps degree q+1.
# Translation g -> g + c is an automorphism of the lift, so distances only need
# to be measured from the representatives (x, 0), one per base vertex x.
# A spanning tree of the base carries voltage 0; the remaining edges get random
# voltages, which are annealed until every pair is within distance D.
# ----------------------------------------------------------------------------

def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _tree_edges(nb, edges):
    """Indices of a spanning tree of the (connected) base graph."""
    adj = [[] for _ in range(nb)]
    for idx, (u, v) in enumerate(edges):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * nb
    seen[0] = True
    tree = set()
    stack = [0]
    while stack:
        x = stack.pop()
        for y, idx in adj[x]:
            if not seen[y]:
                seen[y] = True
                tree.add(idx)
                stack.append(y)
    return tree


def _lift_edges(nb, edges, volt, m):
    """Edge list of the Z_m voltage lift (base edge (u, v) with voltage a joins u*m+g to v*m+(g+a)%m)."""
    out = []
    for (u, v), a in zip(edges, volt):
        for g in range(m):
            out.append((u * m + g, v * m + (g + a) % m))
    return out


def _cost(nb, edges, volt, m, D):
    """Number of ordered (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    N = nb * m
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(edges, volt):
        bu = u * m
        bv = v * m
        for g in range(m):
            x = bu + g
            y = bv + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            b = ball[v]
            for u in adj[v]:
                b |= ball[u]
            new[v] = b
        ball = new
    return sum(N - ball[x * m].bit_count() for x in range(nb))


def _anneal(nb, edges, free, m, D, rng, deadline):
    """Simulated annealing over the free voltages; returns a full voltage list or None."""
    if not free:
        return None
    volt = [0] * len(edges)
    for i in free:
        volt[i] = rng.randrange(m)
    cost = _cost(nb, edges, volt, m, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 3.0, 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = free[rng.randrange(len(free))]
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        c2 = _cost(nb, edges, volt, m, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost = c2
        else:
            volt[i] = old
    return volt


def _search_lifts(nb, edges, d, D, start, time_limit, seed):
    """Search Z_m lifts of the base for the largest m whose lift has diameter <= D."""
    mmax = lib.moore_bound(d, D) // nb
    if mmax < 2:
        return None
    rng = random.Random(seed)
    deadline_all = start + 0.85 * time_limit - 1.0
    tree = _tree_edges(nb, edges)
    free = [i for i in range(len(edges)) if i not in tree]
    best_m = 1
    found = None
    slice_t = 3.0
    while time.monotonic() < deadline_all:
        cands = list(range(mmax, best_m, -1))
        if not cands:
            break
        for m in cands:
            now = time.monotonic()
            if now >= deadline_all:
                break
            dl = min(deadline_all, now + slice_t)
            volt = _anneal(nb, edges, free, m, D, rng, dl)
            if volt is not None:
                best_m = m
                found = (nb * m, _lift_edges(nb, edges, volt, m))
                break
    return found


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            nb, edges = lib.projective_plane_incidence(q)
            if nb > best[0] and lib.is_valid(nb, edges, d, D):
                best = (nb, edges)
            try:
                res = _search_lifts(nb, edges, d, D, start, time_limit, seed)
            except Exception:
                res = None
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
