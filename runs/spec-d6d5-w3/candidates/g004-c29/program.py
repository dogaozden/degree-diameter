import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (cheap, always tried first): projective plane incidence,
# Araujo-Pardo-Lopez graph (D = 3), generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family for D >= 4: near-regular bipartite graphs found by simulated
# annealing over double-edge swaps. The objective is the number of vertex
# pairs at distance greater than D. The sides are kept balanced and every
# vertex has degree exactly d, so the search only moves edges. The graph
# grows adaptively: each size that reaches diameter <= D becomes the new
# base, and the next size is tried with a larger step.
# ----------------------------------------------------------------------------

def _bad_pairs_fast(h, adj, D):
    """Unordered pairs at distance > D in a bipartite graph on 2h vertices (bitmask balls)."""
    n = 2 * h
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    bad = 0
    for x in ball:
        bad += n - x.bit_count()
    return bad // 2


def _rewire(adj, rem, add):
    """Remove the listed undirected edges from adj and insert the new ones."""
    for x, y in rem:
        adj[x].remove(y)
        adj[y].remove(x)
    for x, y in add:
        adj[x].append(y)
        adj[y].append(x)


def _anneal_regular(h, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph on h + h vertices toward diameter <= D.

    Starts from the circulant Haar graph with shifts 0..d-1 (simple since h >= d).
    Returns the edge list on success, or None if the deadline is reached.
    """
    if h < d:
        return None
    n = 2 * h
    edges = [[a, h + (a + s) % h] for a in range(h) for s in range(d)]
    adj = [[] for _ in range(n)]
    keys = set()
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
        keys.add((a, b))

    cost = _bad_pairs_fast(h, adj, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0 = 2.0
    m = len(edges)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = max(0.05, T0 * (1.0 - frac))

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = edges[i]
        c, e = edges[j]
        if a == c or b == e or (a, e) in keys or (c, b) in keys:
            continue

        _rewire(adj, [(a, b), (c, e)], [(a, e), (c, b)])
        new = _bad_pairs_fast(h, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            keys.discard((a, b))
            keys.discard((c, e))
            keys.add((a, e))
            keys.add((c, b))
            edges[i] = [a, e]
            edges[j] = [c, b]
        else:
            _rewire(adj, [(a, e), (c, b)], [(a, b), (c, e)])

    if cost == 0:
        return [(a, b) for a, b in edges]
    return None


def _search_regular(d, D, deadline, rng, best_n, consider):
    """Adaptively grow the side size h; each success is validated and recorded."""
    h_ok = max(d, best_n // 2)
    step = 4
    while time.monotonic() < deadline and step >= 1:
        remaining = deadline - time.monotonic()
        sub = min(deadline, time.monotonic() + max(2.0, 0.45 * remaining))
        h = h_ok + step
        res = _anneal_regular(h, d, D, sub, rng)
        if res is not None:
            consider(2 * h, res)
            h_ok = h
            step = min(step * 2, 64)
        else:
            step //= 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration shortcut: a graph already at the Moore bound cannot be beaten.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: annealed near-regular bipartite graphs, grown adaptively.
    if D >= 4:
        _search_regular(d, D, deadline, rng, best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
