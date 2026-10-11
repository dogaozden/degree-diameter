import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (replaces the voltage-lift search):
#   1. Start from a known regular bipartite base: PG(2,q) incidence for D = 3,
#      the generalized quadrangle W(q) incidence for D >= 4, or K_{d,d}.
#   2. Keep the graph d-regular bipartite at all times. Edge switches
#      (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) preserve degrees and bipartiteness.
#   3. Anneal the switches to minimise the number of vertex pairs at distance > D.
#   4. On success, grow the graph by one vertex pair, using the subdivision-style
#      move: d disjoint edges are rerouted through a new A vertex and a new B
#      vertex, both of degree d. Then anneal again.
#   5. Every recorded graph is checked with lib.is_valid; the base is the fallback.
# ----------------------------------------------------------------------------

GQ_Q_MAX = 7


def _to_edges(h, E):
    """Local pairs (a, b) with a, b in 0..h-1 -> global edges, B vertices offset by h."""
    return [(a, h + b) for a, b in E]


def _kdd(d):
    """K_{d,d} as local pairs."""
    return d, [(i, j) for i in range(d) for j in range(d)]


def _pg_base(q):
    """PG(2, q) incidence graph as local pairs (points x lines)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    return m, [(u, v - m) for u, v in edges]


def _gq_base(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), as local pairs."""
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
    E = [(p, j) for j, L in enumerate(lines) for p in L]
    return P, E


def _bad(h, E, D):
    """Number of unordered vertex pairs at distance > D in the graph given by local pairs E."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _sa(h, E, S, D, deadline, rng, iters):
    """Anneal edge switches to reach zero bad pairs. E and S are updated in place.

    Returns the final cost (0 means the current graph has diameter <= D).
    """
    cost = _bad(h, E, D)
    if cost == 0:
        return 0
    T = max(1.0, 0.02 * cost)
    Tend = 0.15
    decay = (Tend / T) ** (1.0 / iters)
    m = len(E)
    for it in range(iters):
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        T *= decay
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        c2 = _bad(h, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                break
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
    return cost


def _grow(h, E, S, d, rng):
    """Add one A vertex (index h) and one B vertex (index h) of degree d, keeping d-regularity.

    Picks d edges with pairwise distinct endpoints, reroutes them through the new pair.
    Returns False if no such matching is found (state is unchanged then).
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    ua, ub, ch = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        ch.append(idx)
        if len(ch) == d:
            break
    if len(ch) < d:
        return False
    An = h
    Bn = h
    old = [E[idx] for idx in ch]
    for idx, (a, b) in zip(ch, old):
        S.discard((a, b))
        E[idx] = (a, Bn)
        S.add((a, Bn))
    for a, b in old:
        E.append((An, b))
        S.add((An, b))
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    def ok(n, edges):
        return lib.is_valid(n, edges, d, D)

    h0, E0 = _kdd(d)
    if D == 2:
        n, edges = 2 * h0, _to_edges(h0, E0)
        return (n, edges) if ok(n, edges) else (n, edges)

    # Algebraic bases (d - 1 prime power).
    if lib.is_prime_power(d - 1):
        q = d - 1
        if D == 3:
            # PG(2, q) meets the Moore bound for D = 3: nothing to search.
            h, E = _pg_base(q)
            n, edges = 2 * h, _to_edges(h, E)
            if ok(n, edges):
                return n, edges
        elif D >= 4 and q <= GQ_Q_MAX:
            h0, E0 = _gq_base(q)

    base_n, base_edges = 2 * h0, _to_edges(h0, E0)
    if ok(base_n, base_edges):
        best = (base_n, base_edges)
    else:
        h0, E0 = _kdd(d)
        best = (2 * h0, _to_edges(h0, E0))

    rng = random.Random(seed * 7919 + d * 31 + D)
    h = h0
    E = list(E0)
    S = set(E)

    try:
        while time.monotonic() < deadline:
            c = _sa(h, E, S, D, deadline, rng, 3000)
            if c != 0:
                continue
            n = 2 * h
            edges = _to_edges(h, E)
            if n > best[0] and ok(n, edges):
                best = (n, edges)
            if time.monotonic() >= deadline:
                break
            if not _grow(h, E, S, d, rng):
                break
            h += 1
    except Exception:
        pass

    if not ok(best[0], best[1]):
        h0, E0 = _kdd(d)
        return 2 * h0, _to_edges(h0, E0)
    return best
