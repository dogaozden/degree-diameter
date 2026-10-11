import itertools
import math
import random
import time

import lib

_pc = (lambda x: x.bit_count()) if hasattr(int, "bit_count") else (lambda x: bin(x).count("1"))


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) incidence (diameter 4), projective plane
# incidence (diameter 3).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); points first, then lines."""
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


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph state helpers. Graph is bipartite: side[v] in {0, 1}; adjacency as sets.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    ball = _balls(n, adj, D)
    return sum(n - _pc(b) for b in ball) // 2


def _apply(adj, rems, adds):
    for u, v in rems:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in adds:
        adj[u].add(v)
        adj[v].add(u)


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _cover(cands, ball, full, d, rng):
    """Greedy cover of `full` by at most d candidates (randomized tie-breaking)."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and pool and len(chosen) < d:
        gains = [_pc(ball[s] & ~covered) for s in pool]
        mx = max(gains)
        if mx == 0:
            break
        thr = mx - 1 if rng.random() < 0.25 else mx
        idx = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(idx)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen, covered


def _insert(n, adj, d, D, S0, S1, rng):
    """Choose neighbours for a new vertex. Returns (fully_covered, side, neighbours)."""
    ball = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    order = [0, 1]
    rng.shuffle(order)
    for c in order:
        opp = S1 if c == 0 else S0
        cands = [s for s in opp if len(adj[s]) < d]
        chosen, covered = _cover(cands, ball, full, d, rng)
        if covered == full:
            return True, c, chosen
    c = order[0]
    opp = S1 if c == 0 else S0
    cands = [s for s in opp if len(adj[s]) < d]
    chosen, _ = _cover(cands, ball, full, d, rng)
    return False, c, chosen


def _propose(adj, d, S0, S1, rng):
    """Random degree-respecting move: (removals, additions) or None."""
    r = rng.random()
    if r < 0.55:  # edge switch (keeps all degrees)
        a = rng.choice(S0)
        na = adj[a]
        if not na:
            return None
        b = rng.choice(list(na))
        a2 = rng.choice(S0)
        if a2 == a:
            return None
        nb2 = adj[a2]
        if not nb2:
            return None
        b2 = rng.choice(list(nb2))
        if b2 == b or b2 in na or b in nb2:
            return None
        return [(a, b), (a2, b2)], [(a, b2), (a2, b)]
    if r < 0.8:  # add edge between two deficient vertices
        a = rng.choice(S0)
        b = rng.choice(S1)
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            return [], [(a, b)]
        return None
    if r < 0.9:  # remove an edge
        a = rng.choice(S0)
        if not adj[a]:
            return None
        b = rng.choice(list(adj[a]))
        return [(a, b)], []
    # move one endpoint of an edge
    a = rng.choice(S0)
    if not adj[a]:
        return None
    b = rng.choice(list(adj[a]))
    b2 = rng.choice(S1)
    if b2 == b or b2 in adj[a] or len(adj[b2]) >= d:
        return None
    return [(a, b)], [(a, b2)]


def _repair(n, adj, d, D, S0, S1, rng, deadline, steps):
    """Annealing on bad-pair count with fixed vertex set. True if it reaches zero."""
    cur = _bad(n, adj, D)
    for t in range(steps):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            return False
        T = 0.5 * (1.0 - t / steps) + 0.05
        mv = _propose(adj, d, S0, S1, rng)
        if mv is None:
            continue
        rems, adds = mv
        _apply(adj, rems, adds)
        new = _bad(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _apply(adj, adds, rems)
    return cur == 0


def _search(base_n, base_edges, d, D, deadline, rng):
    """Repeatedly insert a vertex (free cover insertion, else insertion + repair); revert on failure."""
    n = base_n
    half = base_n // 2
    side = [0 if v < half else 1 for v in range(n)]
    adj = [set() for _ in range(n)]
    for u, v in base_edges:
        adj[u].add(v)
        adj[v].add(u)
    S0 = [v for v in range(n) if side[v] == 0]
    S1 = [v for v in range(n) if side[v] == 1]
    max_bad = 40

    while time.monotonic() < deadline:
        snap = [set(s) for s in adj]
        n_before = n
        ok, c, chosen = _insert(n, adj, d, D, S0, S1, rng)
        v = n
        n += 1
        side.append(c)
        adj.append(set())
        (S0 if c == 0 else S1).append(v)
        for s in chosen:
            adj[s].add(v)
            adj[v].add(s)
        accepted = ok
        if not ok and _bad(n, adj, D) <= max_bad:
            accepted = _repair(n, adj, d, D, S0, S1, rng, deadline, 300)
        if not accepted:
            adj[:] = snap
            side[:] = side[:n_before]
            n = n_before
            S0[:] = [x for x in range(n) if side[x] == 0]
            S1[:] = [x for x in range(n) if side[x] == 1]
    return n, _edges(n, adj)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5 * time_limit, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    # Moore-optimal for D = 3 when d - 1 is a prime power: return immediately.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        pn, pe = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pn, pe, d, D):
            return pn, pe

    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is None:
        return best_n, best_e

    bn, be = base
    if bn > best_n and lib.is_valid(bn, be, d, D):
        best_n, best_e = bn, be

    if time.monotonic() >= deadline:
        return best_n, best_e

    n, e = _search(bn, be, d, D, deadline, rng)
    if n > best_n and lib.is_valid(n, e, d, D):
        best_n, best_e = n, e
    return best_n, best_e
