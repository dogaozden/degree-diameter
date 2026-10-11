import itertools
import math
import random
import time

import lib

# Island focus: d=16, D=3 (record 394). This version replaces the single-set arc extension
# with two independent point/line arcs (chosen so both have loads <= s = d-q-1), then
# grows the graph one vertex at a time. Each new vertex gets a neighbour set chosen by
# simulated annealing that minimises the number of pairs at distance > D. A vertex is kept
# only when the cost reaches zero, so the graph stays valid. Spare degree on old and new
# vertices is used by the search, including A-B edges.
#
# D >= 4 uses the W(q) generalized-quadrangle baseline. D >= 5 uses K_{d,d} (the voltage-lift
# search of the parent is dropped in this version). Every result is checked with lib.is_valid
# and falls back to K_{d,d}.


# ----------------------------------------------------------------------------
# PG(2,q) data and A/B extensions (diameter 3).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, PL, LP, index) for PG(2, q); lines are indexed by the same vector list."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    PL = [[] for _ in range(m)]   # lines through point i
    LP = [[] for _ in range(m)]   # points on line j
    for u, v in edges:
        PL[u].append(v - m)
        LP[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, PL, LP, index


def _loads_ok(S, covers, m, s):
    load = [0] * m
    for i in S:
        for t in covers[i]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy(covers, m, s, rng, trials, deadline):
    """Randomised greedy: choose items whose covered targets keep every load <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for i in order:
            c = covers[i]
            if all(load[t] < s for t in c):
                S.append(i)
                for t in c:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _base(q, s, rng, deadline):
    """PG(2,q) incidence plus new A-vertices (one per point of SA) and B-vertices (one per line of SB).

    SA and SB are chosen independently. Returns (n, edges, color)."""
    m, edges, PL, LP, index = _pg(q)
    if s <= 0:
        return 2 * m, list(edges), [0] * m + [1] * m
    F = lib.GF(q)
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        conic.append(index[(0, 1, 0)])

    SA = _greedy(PL, m, s, rng, 30, deadline)
    if _loads_ok(conic, PL, m, s) and len(conic) > len(SA):
        SA = conic
    SB = _greedy(LP, m, s, rng, 30, deadline)
    if _loads_ok(conic, LP, m, s) and len(conic) > len(SB):
        SB = conic

    E = list(edges)
    n = 2 * m
    color = [0] * m + [1] * m
    for P in SA:
        x = n
        n += 1
        color.append(0)
        for L in PL[P]:
            E.append((x, m + L))
    for j in SB:
        y = n
        n += 1
        color.append(1)
        for Q in LP[j]:
            E.append((Q, y))
    return n, E, color


# ----------------------------------------------------------------------------
# Incremental annealing search: add vertices one at a time.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Twice the number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _try_add(adj, color, d, D, c, deadline, rng, iters):
    """Try to add one vertex of colour c whose neighbours have the opposite colour. Keep it only if cost is 0."""
    n = len(adj)
    cands = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
    if not cands:
        return False
    x = n
    adj.append(set())
    color.append(c)
    N = set(rng.sample(cands, min(d, len(cands))))
    adj[x] = set(N)
    for u in N:
        adj[u].add(x)
    cost = _bad(n + 1, adj, D)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.15, T * 0.99)
        cands = [v for v in range(n) if color[v] != c and len(adj[v]) < d and v not in N]
        if len(N) < d and (not N or rng.random() < 0.2):
            if not cands:
                continue
            w = rng.choice(cands)
            N.add(w)
            adj[w].add(x)
            adj[x].add(w)
            new_cost = _bad(n + 1, adj, D)
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new_cost
            else:
                N.discard(w)
                adj[w].discard(x)
                adj[x].discard(w)
        else:
            if not cands:
                continue
            u = rng.choice(list(N))
            w = rng.choice(cands)
            N.discard(u)
            adj[u].discard(x)
            adj[x].discard(u)
            N.add(w)
            adj[w].add(x)
            adj[x].add(w)
            new_cost = _bad(n + 1, adj, D)
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new_cost
            else:
                N.discard(w)
                adj[w].discard(x)
                adj[x].discard(w)
                N.add(u)
                adj[u].add(x)
                adj[x].add(u)
    if cost == 0:
        return True
    for u in N:
        adj[u].discard(x)
    adj.pop()
    color.pop()
    return False


def _extend(d, D, adj, color, deadline, rng):
    """Repeatedly try to add vertices; stop after several consecutive failures or at the deadline."""
    fails = 0
    while time.monotonic() < deadline and fails < 8:
        c = rng.randrange(2)
        if _try_add(adj, color, d, D, c, deadline, rng, 300):
            fails = 0
        else:
            fails += 1


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d >= 3:
        q = max(qq for qq in range(2, d) if lib.is_prime_power(qq))
        s = d - q - 1
        n, E, color = _base(q, s, rng, start + 0.25 * time_limit)
        consider(n, E)
        adj = [set() for _ in range(n)]
        for u, v in E:
            adj[u].add(v)
            adj[v].add(u)
        if max(len(a) for a in adj) <= d and _bad(n, adj, D) == 0:
            _extend(d, D, adj, color, deadline, rng)
            n2 = len(adj)
            E2 = [(u, v) for u in range(n2) for v in adj[u] if u < v]
            consider(n2, E2)
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
