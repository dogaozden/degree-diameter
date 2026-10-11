import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines (kept as safe starting points).
#   D = 3: incidence graph of PG(2, q), q + 1 <= d (meets the Moore bound when d - 1 = q).
#   D >= 4: incidence graph of the generalized quadrangle W(q), diameter 4.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: unstructured regular bipartite graphs found by
# simulated annealing with degree-preserving double-edge swaps, grown one
# vertex pair at a time. Each level n = 2h is a d-regular bipartite graph
# that is repaired (if needed) until its diameter is at most D.
# ----------------------------------------------------------------------------

def _dist_cost(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (disconnected pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _rep(lst, old, new):
    """Replace entry old by new in list lst (old must be present)."""
    lst[lst.index(old)] = new


def _swap(E, adj, S, i, j):
    """Double-edge swap of edges E[i]=(a1,b1), E[j]=(a2,b2) into (a1,b2), (a2,b1).

    It is an involution: applying it again to the same indices restores the old state.
    """
    a1, b1 = E[i]
    a2, b2 = E[j]
    _rep(adj[a1], b1, b2)
    _rep(adj[b1], a1, a2)
    _rep(adj[a2], b2, b1)
    _rep(adj[b2], a2, a1)
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal(n, adj, E, S, D, rng, deadline):
    """Anneal swaps until the diameter bound holds. True on success, False at deadline."""
    cost = _dist_cost(n, adj, D)
    m = len(E)
    t0 = time.monotonic()
    T = 1.0
    it = 0
    while cost > 0:
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                return False
            # Reheat every 4 seconds so the walk keeps exploring plateaus.
            phase = ((now - t0) % 4.0) / 4.0
            T = 1.2 * (0.04 / 1.2) ** phase
        it += 1
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        _swap(E, adj, S, i, j)
        c2 = _dist_cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(E, adj, S, i, j)
    return True


def _grow_one(n, adj, E, S, d, rng):
    """Add one A vertex and one B vertex, each of degree d, keeping regularity.

    Pick a matching of d edges (x_k, y_k). Replace them by (x_k, nb) and (na, y_k).
    Returns (n + 2, new_E), or None if no suitable matching was found.
    """
    m = len(E)
    pick = None
    for _ in range(300):
        order = list(range(m))
        rng.shuffle(order)
        usedA = set()
        usedB = set()
        cand = []
        for idx in order:
            a, b = E[idx]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            cand.append(idx)
            if len(cand) == d:
                break
        if len(cand) == d:
            pick = cand
            break
    if pick is None:
        return None

    xs = [E[k][0] for k in pick]
    ys = [E[k][1] for k in pick]
    na, nb = n, n + 1
    drop = set(pick)
    for x, y in zip(xs, ys):
        S.discard((x, y))
        _rep(adj[x], y, nb)
        _rep(adj[y], x, na)
    adj.append(list(ys))
    adj.append(list(xs))
    newE = [e for k, e in enumerate(E) if k not in drop]
    for y in ys:
        newE.append((na, y))
        S.add((na, y))
    for x in xs:
        newE.append((x, nb))
        S.add((x, nb))
    return n + 2, newE


def _growth_search(d, D, moore, deadline, rng, consider):
    """Start from K_{d,d} and grow one vertex pair at a time, repairing by annealing."""
    h = d
    n = 2 * d
    adj = [[] for _ in range(n)]
    E = []
    for i in range(d):
        for s in range(d):
            a, b = i, d + (i + s) % d
            E.append((a, b))
            adj[a].append(b)
            adj[b].append(a)
    S = set(E)

    while time.monotonic() < deadline:
        cost = _dist_cost(n, adj, D)
        if cost == 0:
            consider(n, list(E))
            if n + 2 > moore:
                break
            res = _grow_one(n, adj, E, S, d, rng)
            if res is None:
                break
            n, E = res
            continue
        if not _anneal(n, adj, E, S, D, rng, deadline):
            break


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] < moore:
        _growth_search(d, D, moore, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
