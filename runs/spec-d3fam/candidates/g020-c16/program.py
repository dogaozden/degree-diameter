import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions (validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family (D = 3): grow the record graph by two vertices, then repair the
# diameter with degree-preserving 2-switch simulated annealing.
#
# Growth: pick a matching M of k edges (x_i, y_i), x_i in A, y_i in B. Delete
# them, add a new A-vertex a adjacent to all y_i and a new B-vertex b adjacent
# to all x_i. Every old vertex keeps its degree and every new vertex has degree
# k <= d, so the result is bipartite with max degree <= d.
#
# Repair: 2-switch on edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). This keeps all
# degrees and bipartiteness. Cost = number of unordered pairs at distance > D.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Proper 2-colouring of a bipartite graph given as an edge list."""
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


def _cost3(n, adj, D):
    """Unordered pairs at distance > D, computed with bitmask ball expansion."""
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


def _set_edge(adj, S, E, n, i, a, b):
    """Replace the i-th edge of E by (a, b), keeping adjacency lists and key set S in sync."""
    oa, ob = E[i]
    adj[oa].remove(ob)
    adj[ob].remove(oa)
    S.discard(oa * n + ob)
    adj[a].append(b)
    adj[b].append(a)
    S.add(a * n + b)
    E[i] = (a, b)


def _extend2(n, E, d, rng):
    """Add two vertices (new A-vertex n, new B-vertex n+1) by re-routing a random matching."""
    order = list(range(len(E)))
    rng.shuffle(order)
    used = set()
    M = []
    for idx in order:
        a, b = E[idx]
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        M.append(idx)
        if len(M) == d:
            break
    if len(M) < 2:
        return None
    Mset = set(M)
    newE = [E[i] for i in range(len(E)) if i not in Mset]
    a_new, b_new = n, n + 1
    for idx in M:
        x, y = E[idx]
        newE.append((a_new, y))   # new A-vertex to old B-vertex
        newE.append((x, b_new))   # old A-vertex to new B-vertex
    return n + 2, newE


def _anneal_ext(n, E0, D, rng, deadline):
    """Anneal 2-switches to drive the pair-distance cost to zero. Returns edge list or None."""
    E = list(E0)
    adj = [[] for _ in range(n)]
    S = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        S.add(a * n + b)
    cost = _cost3(n, adj, D)
    if cost == 0:
        return E
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 1.0 * (0.05 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1 * n + b2) in S or (a2 * n + b1) in S:
            continue
        _set_edge(adj, S, E, n, i, a1, b2)
        _set_edge(adj, S, E, n, j, a2, b1)
        new = _cost3(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            if cost == 0:
                return E
        else:
            _set_edge(adj, S, E, n, j, a2, b2)
            _set_edge(adj, S, E, n, i, a1, b1)
    return None


def _search3(n0, e0, d, D, deadline, rng, consider):
    """Repeatedly grow the current valid graph by 2 vertices and repair; keep every success."""
    color = _two_color(n0, e0)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in e0]
    n = n0
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 2.0:
            break
        slice_end = now + min(remaining, max(4.0, remaining / 3))
        ext = _extend2(n, E, d, rng)
        if ext is None:
            break
        n2, E2 = ext
        res = _anneal_ext(n2, E2, D, rng, slice_end)
        if res is None:
            continue
        edges = [(a, b) for a, b in res]
        if lib.is_valid(n2, edges, d, D):
            consider(n2, edges)
            n, E = n2, list(res)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3:
        for builder in (_ara, _best_pg):
            try:
                cand = builder(d)
                if cand is not None:
                    consider(cand[0], cand[1])
            except Exception:
                pass

    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Bold new search: only for D = 3, skipped when already at the Moore bound.
    if D == 3 and d >= 5 and best_n < lib._moore_bound(d, D):
        try:
            _search3(best_n, best_e, d, D, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
