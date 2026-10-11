import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known constructions (safe baselines).
# ----------------------------------------------------------------------------

def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg_for(d):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW bold family (diameter 3): vertex-pair insertion into a regular bipartite
# record graph, followed by degree-preserving 2-switch annealing that drives the
# number of pairs at distance > 3 to zero. Every intermediate graph is d-regular
# and bipartite, so only diameter needs repair.
# ----------------------------------------------------------------------------

def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _oriented(n, edges):
    """Orient each edge as (side0, side1) using a 2-colouring."""
    adj = lib.adjacency(n, edges)
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
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D, using bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _set_pair(E, S, adj, i, j, old_i, old_j, new_i, new_j):
    for a, b in (old_i, old_j):
        S.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in (new_i, new_j):
        S.add((a, b))
        adj[a].add(b)
        adj[b].add(a)
    E[i] = new_i
    E[j] = new_j


def _insert_pair(n, E, S, adj, d, rng):
    """Add vertices x (side 0) and y (side 1), each of degree d, by splitting d disjoint edges."""
    order = list(range(len(E)))
    rng.shuffle(order)
    ua, ub, chosen = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    for i in chosen:
        a, b = E[i]
        S.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
        E[i] = (x, b)
        S.add((x, b))
        adj[x].add(b)
        adj[b].add(x)
        E.append((a, y))
        S.add((a, y))
        adj[a].add(y)
        adj[y].add(a)
    return True


def _anneal(n, E, S, adj, D, deadline, rng):
    """2-switch annealing until diameter <= D holds (cost 0) or the deadline passes."""
    cur = _bad_pairs(n, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.6 * (0.02 ** ((now - start) / span))
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        _set_pair(E, S, adj, i, j, (a1, b1), (a2, b2), n1, n2)
        new = _bad_pairs(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _set_pair(E, S, adj, i, j, n1, n2, (a1, b1), (a2, b2))
    return cur == 0


def _grow_d3(n, E, d, D, deadline, rng, moore):
    """Repeatedly insert a vertex pair and repair; keep the largest diameter-3 state."""
    S = set(E)
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    best_n, best_E = n, list(E)
    fails = 0
    while fails < 2 and time.monotonic() < deadline and n + 2 <= moore:
        saved = (n, list(E), set(S), [set(s) for s in adj])
        now = time.monotonic()
        budget = max(1.0, 0.5 * (deadline - now))
        if not _insert_pair(n, E, S, adj, d, rng):
            break
        n += 2
        if _anneal(n, E, S, adj, D, min(deadline, now + budget), rng):
            best_n, best_E = n, list(E)
            fails = 0
        else:
            n, E, S, adj = saved
            fails += 1
    return best_n, best_E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    bases = []
    if D >= 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
            bases.append(ara)
        pg = _pg_for(d)
        if pg is not None:
            consider(pg[0], pg[1])
            bases.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D == 3 and d >= 3:
        # Bold path: grow the largest d-regular base by vertex-pair insertion and repair.
        regular = [b for b in bases if _is_regular(b[0], b[1], d)]
        if regular:
            n0, e0 = max(regular, key=lambda b: b[0])
            E = _oriented(n0, e0)
            moore = lib.moore_bound(d, D)
            n2, E2 = _grow_d3(n0, E, d, D, deadline, rng, moore)
            consider(n2, [(int(u), int(v)) for u, v in E2])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
