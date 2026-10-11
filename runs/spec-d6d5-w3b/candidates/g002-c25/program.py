import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic seeds: projective plane, generalized quadrangle, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3 (valid for D >= 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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


def _gq_candidate(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 7 for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Direct search on bipartite graphs: start from a random-shift Haar graph
# (a simple d-regular bipartite graph), anneal with 2-switches on the
# number of ordered vertex pairs at distance > D, then grow by splicing
# two new vertices (one per side) and annealing again.
#
# Convention: each edge is a tuple (a, b) with a on the left, b on the right.
# Left vertices and right vertices are only distinguished by this orientation.
# ----------------------------------------------------------------------------

def _adj(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _dist_cost(n, adj, D):
    """Ordered count of (vertex, vertex) pairs at distance > D (bitmask BFS). Zero means valid."""
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


def _splice_pair(n, E, d, rng):
    """Insert a left vertex x=n and a right vertex y=n+1 of degree d by splicing d edges.

    Old degrees are preserved. Returns (n + 2, new_edges) or None.
    """
    m = len(E)
    if m < d:
        return None
    x, y = n, n + 1
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 50000:
        tries += 1
        i = rng.randrange(m)
        if i in used:
            continue
        a, b = E[i]
        if b in xs or a in ys:
            continue
        used.add(i)
        xs.add(b)
        ys.add(a)
        chosen.append(i)
    if len(chosen) < d:
        return None
    newE = [E[i] for i in range(m) if i not in used]
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return n + 2, newE


def _anneal(n, E, D, deadline, rng, T0=2.0):
    """Anneal 2-switches (a,b),(c,e) -> (a,e),(c,b) to drive the distance-violation cost to 0.

    Returns the edge list on success, or None if the deadline passes first.
    """
    m = len(E)
    if m < 2:
        return None
    eset = set(E)
    cur = _dist_cost(n, _adj(n, E), D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it = 0
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        it += 1
        if it % 20 == 0:
            frac = (now - start) / span
            T = max(0.05, T0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = _dist_cost(n, _adj(n, E), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return E if cur == 0 else None


def _haar_edges(side, S):
    """Haar-type bipartite graph: left i ~ right j iff j - i in S (mod side). Simple and d-regular."""
    return [(i, j) for i in range(side) for j in ((i + s) % side for s in S)]


def _search_family(d, D, best_n, deadline, rng, consider):
    """Random Haar start, anneal to diameter D, then grow by splice + anneal."""
    side = max(d + 1, best_n // 2 - 20)
    E, n = None, None
    # Find a starting size that anneals to validity.
    while time.monotonic() < deadline - 1.0:
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(3.0, remaining / 2.0))
        S = rng.sample(range(side), d)
        E0 = [(i, side + j) for i, j in _haar_edges(side, S)]
        n0 = 2 * side
        # Re-index right vertices as side + j so left and right ids are disjoint.
        res = _anneal(n0, E0, D, slice_end, rng)
        if res is not None:
            n, E = n0, res
            consider(n, E)
            break
        if side <= d + 1:
            return
        side = max(d + 1, side - 8)
    if E is None:
        return
    # Grow: splice two vertices, then repair by annealing.
    while time.monotonic() < deadline - 1.0:
        sp = _splice_pair(n, E, d, rng)
        if sp is None:
            break
        n2, E2 = sp
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(3.0, remaining / 2.0))
        res = _anneal(n2, E2, D, slice_end, rng)
        if res is None:
            break
        n, E = n2, res
        consider(n, E)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
            return True
        return False

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _gq_candidate(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # The direct search is the new family; it runs for D >= 4 with d >= 3.
    if D >= 4 and d >= 3:
        _search_family(d, D, best_n, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
