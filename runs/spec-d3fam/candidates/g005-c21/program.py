"""Search-based repair growth for diameter-3 bipartite graphs.

Strategy for D = 3:
  1. Start from the best known algebraic base (Araujo-Pardo & Lopez graph when
     d - 2 is a prime power, otherwise the projective plane incidence graph).
  2. Add t new vertices (t = 1, then 2, ...), with random sides.
  3. Fill spare degree greedily, then run simulated annealing over degree-preserving
     2-switches and degree-moving "transfers" toward deficient vertices. The energy is
     the number of vertex pairs at distance > 3. Any zero-energy state is verified
     with lib.is_valid before it is accepted.

Every candidate is checked with lib.is_valid, so the best valid graph found is returned.
For D >= 4 the program uses the generalized quadrangle W(q) and a K_{d,d} fallback.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Diameter-3 search helpers.
# ----------------------------------------------------------------------------

def _bad(n, adj):
    """Number of unordered pairs at distance > 3 (adj is a list of sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _color(n, nbrs):
    """Two-colouring of a bipartite graph given by neighbour lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in nbrs[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _saturate(n, adj, side, d, rng):
    """Randomly add edges between opposite-side vertices that both have spare degree."""
    L = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    R = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in L for b in R if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _move_switch(S0, adj, rng):
    """Degree-preserving 2-switch: a-b, c-e  ->  a-e, c-b. Returns undo token or None."""
    a = rng.choice(S0)
    if not adj[a]:
        return None
    b = rng.choice(tuple(adj[a]))
    c = rng.choice(S0)
    if not adj[c]:
        return None
    e = rng.choice(tuple(adj[c]))
    if a == c or b == e or e in adj[a] or b in adj[c]:
        return None
    adj[a].discard(b); adj[b].discard(a)
    adj[c].discard(e); adj[e].discard(c)
    adj[a].add(e); adj[e].add(a)
    adj[c].add(b); adj[b].add(c)
    return ('s', a, b, c, e)


def _move_transfer(n, side, adj, d, rng):
    """Move an edge a-b to x-b, where x is a deficient vertex. Returns undo token or None."""
    deficient = [v for v in range(n) if len(adj[v]) < d]
    if not deficient:
        return None
    x = rng.choice(deficient)
    cands = [b for b in range(n) if side[b] != side[x] and b not in adj[x] and adj[b]]
    if not cands:
        return None
    b = rng.choice(cands)
    a = rng.choice(tuple(adj[b]))
    adj[a].discard(b); adj[b].discard(a)
    adj[x].add(b); adj[b].add(x)
    return ('t', x, b, a)


def _undo(adj, u):
    if u[0] == 's':
        _, a, b, c, e = u
        adj[a].discard(e); adj[e].discard(a)
        adj[c].discard(b); adj[b].discard(c)
        adj[a].add(b); adj[b].add(a)
        adj[c].add(e); adj[e].add(c)
    else:
        _, x, b, a = u
        adj[x].discard(b); adj[b].discard(x)
        adj[a].add(b); adj[b].add(a)


def _attempt(n0, edges, t, d, D, deadline, rng):
    """Try to extend a valid diameter-3 bipartite graph by t vertices. Returns (n, edges) or None."""
    n = n0 + t
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    base_col = _color(n0, [list(adj[v]) for v in range(n0)])
    off = rng.randrange(2)
    side = base_col + [(i + off) % 2 for i in range(t)]
    S0 = [v for v in range(n) if side[v] == 0]

    _saturate(n, adj, side, d, rng)
    cost = _bad(n, adj)

    T0, T1 = 1.5, 0.15
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        it += 1
        if it % 50 == 0:
            _saturate(n, adj, side, d, rng)
            cost = _bad(n, adj)
            if cost == 0:
                break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac
        if rng.random() < 0.5:
            undo = _move_switch(S0, adj, rng)
        else:
            undo = _move_transfer(n, side, adj, d, rng)
        if undo is None:
            continue
        c2 = _bad(n, adj)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _undo(adj, undo)

    E = [(u, v) for u in range(n) if side[u] == 0 for v in adj[u]]
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


def _grow(cur, d, D, deadline, rng):
    """Repeatedly add 1 (or 2) vertices by annealing until time runs out."""
    n, e = cur
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        res = _attempt(n, e, 1, d, D, time.monotonic() + 0.5 * remaining, rng)
        if res is None:
            res = _attempt(n, e, 2, d, D, deadline, rng)
        if res is None:
            break
        n, e = res
    return n, e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for cand in (_ara(d), _pg(d)):
            if cand is not None:
                consider(cand[0], cand[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D == 3 and best_n > 0:
        n2, e2 = _grow(best, d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
