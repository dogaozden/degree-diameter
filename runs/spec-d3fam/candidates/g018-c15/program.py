import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (kept from the parent as the safe fallback chain).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2, order 2(q^2+q+5)) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Helpers for the new search.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _bad(nbrs, n, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbrs[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# New bold family: grow a d-regular bipartite D=3 graph by two vertices, then
# anneal degree-preserving 2-switches to remove all bad pairs.
# ----------------------------------------------------------------------------

def _sa_grow(n0, edges0, color0, d, D, deadline, rng):
    """Add a left vertex x and a right vertex y, both of degree d, then anneal to diameter <= D.

    Returns (n, edges, color) on success, None on failure.
    """
    n = n0 + 2
    x, y = n0, n0 + 1
    color = list(color0) + [0, 1]
    E = []
    for u, v in edges0:
        E.append((u, v) if color[u] == 0 else (v, u))
    nbrs = [set() for _ in range(n)]
    for a, b in E:
        nbrs[a].add(b)
        nbrs[b].add(a)

    # Fill: each move takes a base edge (a,b) and replaces it by (a,y), (x,b).
    # Both a and b keep their degrees; x and y each gain one neighbour.
    tries = 0
    while len(nbrs[x]) < d:
        tries += 1
        if tries > 200000:
            return None
        i = rng.randrange(len(E))
        a, b = E[i]
        if b in nbrs[x] or a in nbrs[y]:
            continue
        E[i] = (a, y)
        nbrs[a].discard(b)
        nbrs[b].discard(a)
        nbrs[a].add(y)
        nbrs[y].add(a)
        E.append((x, b))
        nbrs[x].add(b)
        nbrs[b].add(x)

    cost = _bad(nbrs, n, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in nbrs[a] or b in nbrs[c]:
            continue
        # Apply 2-switch: (a,b),(c,e) -> (a,e),(c,b). Degrees preserved, bipartite preserved.
        nbrs[a].discard(b)
        nbrs[b].discard(a)
        nbrs[c].discard(e)
        nbrs[e].discard(c)
        nbrs[a].add(e)
        nbrs[e].add(a)
        nbrs[c].add(b)
        nbrs[b].add(c)
        new = _bad(nbrs, n, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            nbrs[a].discard(e)
            nbrs[e].discard(a)
            nbrs[c].discard(b)
            nbrs[b].discard(c)
            nbrs[a].add(b)
            nbrs[b].add(a)
            nbrs[c].add(e)
            nbrs[e].add(c)
    return n, E, color


def _grow_regular(n, edges, d, D, deadline, rng):
    """Repeatedly grow a regular bipartite graph by two vertices while the annealer succeeds."""
    cur_n, cur_e = n, list(edges)
    cur_c = _two_color(cur_n, cur_e)
    best = (cur_n, cur_e)
    while True:
        rem = deadline - time.monotonic()
        if rem < 0.5:
            break
        res = _sa_grow(cur_n, cur_e, cur_c, d, D, time.monotonic() + 0.6 * rem, rng)
        if res is None:
            break
        cur_n, cur_e, cur_c = res
        best = (cur_n, list(cur_e))
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])

        # Bold D=3 family: grow the best d-regular base graph by annealing.
        if D == 3 and d >= 3:
            bases = [g for g in (rec, pg) if g is not None]
            for base_n, base_e in sorted(bases, key=lambda g: -g[0]):
                if base_n >= lib._moore_bound(d, D):
                    continue  # already at the Moore bound
                if not _is_regular(base_n, base_e, d):
                    continue
                grown_n, grown_e = _grow_regular(base_n, base_e, d, D,
                                                 deadline, random.Random(seed + 17))
                consider(grown_n, grown_e)
                break

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
