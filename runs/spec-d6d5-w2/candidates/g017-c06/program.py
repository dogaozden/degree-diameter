import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence graphs (diameter 3), the
# Araujo-Pardo-Lopez graph for d = q + 2, and greedy cover/saturation growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: unstructured d-regular bipartite graphs found by
# "layer-swap" annealing.
#
# A simple d-regular bipartite graph on parts A = {0..h-1}, B = {h..2h-1} is
# the union of d perfect matchings, layer i matching a to h + sig[i][a], where
# every sig[i] is a permutation of range(h). Starting from a Haar graph
# (sig[i][a] = a + s_i), the move "swap sig[i][a] and sig[i][b]" keeps every
# sig[i] a permutation, so the graph stays d-regular on both sides. The only
# constraint is that a and b gain no duplicate neighbour, which is checked
# before the move. The cost is the number of ordered (vertex, vertex) pairs at
# distance more than D (zero means diameter <= D). Random regular graphs of
# this size have only a few bad pairs, so annealing can push past algebraic
# records at this scale.
# ----------------------------------------------------------------------------

def _regular_cost(h, d, sig, D):
    """Ordered pairs at distance > D in the layered bipartite graph (zero iff diameter <= D)."""
    N = 2 * h
    adj = [[] for _ in range(N)]
    for row in sig:
        for a in range(h):
            b = h + row[a]
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N - b.bit_count() for b in ball)


def _anneal_regular(h, d, D, deadline, rng):
    """Anneal layer-swap moves from a Haar start until diameter <= D or the deadline. Returns sig or None."""
    shifts = rng.sample(range(h), d)
    sig = [[(a + s) % h for a in range(h)] for s in shifts]
    cost = _regular_cost(h, d, sig, D)
    if cost == 0:
        return sig
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t0) / span)
        T = 3.0 * (1.0 - frac) + 0.2 * frac
        i = rng.randrange(d)
        a = rng.randrange(h)
        b = rng.randrange(h)
        if a == b:
            continue
        x = sig[i][a]
        y = sig[i][b]
        bad = False
        for j in range(d):
            if j != i and (sig[j][a] == y or sig[j][b] == x):
                bad = True
                break
        if bad:
            continue
        sig[i][a] = y
        sig[i][b] = x
        c2 = _regular_cost(h, d, sig, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
            if cost == 0:
                return sig
        else:
            sig[i][a] = x
            sig[i][b] = y


def _regular_edges(h, d, sig):
    """Edge list of the layered graph: 2h vertices, A = 0..h-1, B = h..2h-1."""
    E = [(a, h + sig[i][a]) for i in range(d) for a in range(h)]
    return 2 * h, E


def _regular_phase(d, D, best_n, deadline, rng, consider):
    """Climb the part size h upward, annealing a regular graph at each size; budgets grow on failure."""
    h = max(d, best_n // 2 + 1)
    fails = 0
    while time.monotonic() < deadline:
        budget = min(deadline - time.monotonic(), 8.0 * (1 + fails))
        if budget <= 0.05:
            break
        sig = _anneal_regular(h, d, D, time.monotonic() + budget, rng)
        if sig is not None:
            n, e = _regular_edges(h, d, sig)
            consider(n, e)
            h += 1
            fails = 0
        else:
            fails += 1


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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # New family: annealed unstructured regular bipartite graphs for D >= 4.
    if D >= 4 and d >= 3:
        _regular_phase(d, D, best_n, deadline, random.Random(seed * 2654435761 + d * 97 + D),
                       consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
