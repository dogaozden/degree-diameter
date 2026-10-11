import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 1200           # annealing steps per growth attempt
MAX_FAILS = 6         # consecutive failed growth attempts before stopping
PAIR_PROB = 0.6       # probability a growth step inserts a balanced pair
TARGET_BIAS = 0.7     # probability a swap starts from a vertex with bad pairs


# ---------------------------------------------------------------- helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
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
    return color


def _balls_adj(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _costs(n, adj, D):
    """Return (total bad pairs, bad count per vertex). Unreachable pairs count as bad."""
    reach = _balls_adj(n, adj, D)
    bad = [n - r.bit_count() for r in reach]
    return sum(bad) // 2, bad


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- local moves

def _pick_neighbours(n, adj, color, c, k, D, rng):
    """Choose k vertices of colour 1-c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < k:
        return None
    balls = _balls_adj(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < k and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    chosen += rest[:k - len(chosen)]
    return chosen


def _swap(adj, side0, bad, rng):
    """Degree-preserving double-edge swap keeping bipartiteness, biased to bad vertices."""
    hot = None
    if rng.random() < TARGET_BIAS:
        hot = [v for v in side0 if bad[v] > 0]
    a1 = rng.choice(hot) if hot else rng.choice(side0)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(side0)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    adj[a1].remove(b1); adj[b1].remove(a1)
    adj[a2].remove(b2); adj[b2].remove(a2)
    adj[a1].add(b2); adj[b2].add(a1)
    adj[a2].add(b1); adj[b1].add(a2)
    return (a1, b1, a2, b2)


def _unswap(adj, mv):
    a1, b1, a2, b2 = mv
    adj[a1].remove(b2); adj[b2].remove(a1)
    adj[a2].remove(b1); adj[b1].remove(a2)
    adj[a1].add(b1); adj[b1].add(a1)
    adj[a2].add(b2); adj[b2].add(a2)


def _augment(n, adj, color, d, rng):
    """Add edges between deficient opposite-colour vertices. Never breaks the diameter bound."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not d0 or not d1:
        return
    rng.shuffle(d0)
    for u in d0:
        if len(adj[u]) >= d:
            continue
        for v in d1:
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                if len(adj[u]) >= d:
                    break


def _grow(n, adj, color, d, D, rng, deadline, pair):
    """Insert one vertex, or a balanced pair joined by an edge, then anneal until the
    diameter bound holds. Returns new (n, adj, color) or None."""
    adj = [set(s) for s in adj]
    color = list(color)
    if pair:
        specs = [(0, d - 1), (1, d - 1)]
    else:
        specs = [(rng.randrange(2), d)]

    # Pick neighbours on the old graph for every new vertex.
    picks = []
    for c, k in specs:
        nb = _pick_neighbours(n, adj, color, c, k, D, rng)
        if nb is None:
            return None
        picks.append(nb)

    # Free degree at the chosen neighbours.
    for nb in picks:
        for u in nb:
            if len(adj[u]) >= d:
                w = rng.choice(tuple(adj[u]))
                adj[u].discard(w)
                adj[w].discard(u)

    # Attach the new vertices.
    for (c, _), nb in zip(specs, picks):
        x = n
        adj.append(set())
        color.append(c)
        n += 1
        for u in nb:
            adj[x].add(u)
            adj[u].add(x)
    if pair:
        adj[n - 2].add(n - 1)
        adj[n - 1].add(n - 2)

    # Anneal with targeted swaps.
    side0 = [v for v in range(n) if color[v] == 0]
    cost, bad = _costs(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, bad, rng)
        if mv is None:
            continue
        new, nbad = _costs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost, bad = new, nbad
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    _augment(n, adj, color, d, rng)
    return n, adj, color


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Starting candidates (all verified with lib.is_valid).
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    kdd = lib.haar_graph(d, range(d))
    bases.append(kdd)
    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return kdd
    base_n, base_e = max(valid, key=lambda c: c[0])

    color = _two_colour(base_n, base_e)
    adj = [set() for _ in range(base_n)]
    for u, v in base_e:
        adj[u].add(v)
        adj[v].add(u)
    cur_n, cur_adj, cur_col = base_n, adj, color
    best_n, best_e = base_n, base_e

    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        pair = rng.random() < PAIR_PROB
        res = _grow(cur_n, cur_adj, cur_col, d, D, rng, deadline, pair)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur_n, cur_adj, cur_col = res
        if cur_n > best_n:
            cand_e = _edges(cur_n, cur_adj)
            if lib.is_valid(cur_n, cand_e, d, D):
                best_n, best_e = cur_n, cand_e

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
