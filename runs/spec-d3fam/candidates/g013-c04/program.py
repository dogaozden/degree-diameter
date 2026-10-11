import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used before returning
MARGIN = 3.0          # seconds kept in reserve
ANNEAL_ITER = 1200    # swap steps per growth attempt
MAX_FAILS = 6         # consecutive failed growth attempts before stopping


# ---------------------------------------------------------------- graph utils

def _adjacency(n, edges):
    """Adjacency as a list of sets."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edge_list(n, adj):
    """Edge list (u < v) from set-based adjacency."""
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _two_colour(n, adj):
    """Proper 2-colouring of a bipartite graph, component by component."""
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


def _balls(n, adj, r):
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = _balls(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power <= d - 1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- cover growth

def _greedy_cover(pool, balls, full, d, rng, randomize):
    """Greedy cover of `full` by at most d pool vertices (their D-1 balls). None if it fails."""
    pool = list(pool)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(balls[s] & ~covered).bit_count() for s in pool]
        best = max(gains)
        if best == 0:
            break
        if randomize:
            slack = 1 if rng.random() < 0.3 else 0
            ok = [i for i, g in enumerate(gains) if g > 0 and g >= best - slack]
            i = rng.choice(ok)
        else:
            i = gains.index(best)
        s = pool.pop(i)
        chosen.append(s)
        covered |= balls[s]
    return chosen if covered == full else None


def _cover_vertex(n, adj, color, d, D, rng, tries=24):
    """Find a new vertex's neighbourhood: deficient vertices whose radius-(D-1) balls cover all.

    Returns (c, chosen) where the new vertex gets colour c and neighbours have colour 1 - c.
    Any such addition keeps the diameter bound, since distances can only shrink.
    """
    balls = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    order = [0, 1]
    rng.shuffle(order)
    for c in order:
        pool = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
        if not pool:
            continue
        for t in range(tries):
            chosen = _greedy_cover(pool, balls, full, d, rng, t > 0)
            if chosen is not None:
                return c, chosen
    return None


def _cover_grow(n, adj, color, d, D, rng, deadline):
    """Repeatedly add cover vertices. Mutates adj and color; returns the new vertex count."""
    while time.monotonic() < deadline:
        res = _cover_vertex(n, adj, color, d, D, rng)
        if res is None:
            break
        c, chosen = res
        x = n
        n += 1
        adj.append(set())
        color.append(c)
        for s in chosen:
            adj[s].add(x)
            adj[x].add(s)
    return n


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


# ---------------------------------------------------------------- annealing growth

def _pick_neighbours(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1 - c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < d and cand:
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
    chosen += rest[:d - len(chosen)]
    return chosen


def _swap(adj, side0, rng):
    """Degree-preserving double-edge swap keeping bipartiteness. Returns undo info or None."""
    a1 = rng.choice(side0)
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


def _attempt(n, adj, color, d, D, rng, deadline):
    """Add one vertex and anneal swaps until the diameter bound holds. Returns (n, adj, color) or None."""
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick_neighbours(n, adj, color, c, d, D, rng)
    if nb is None:
        return None
    for u in nb:
        if len(adj[u]) >= d:
            w = rng.choice(tuple(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for u in nb:
        adj[x].add(u)
        adj[u].add(x)

    side0 = [v for v in range(n) if color[v] == 0]
    cost = _bad_pairs(n, adj, D)
    for it in range(ANNEAL_ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ANNEAL_ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
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
    if d == 2:                                   # even cycle of length 2D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                   # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):     # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    kdd = lib.haar_graph(d, range(d))
    try:
        cands = [kdd]
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))   # record family, degree d
            except Exception:
                pass
        valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
        if not valid:
            return kdd
        base_n, base_e = max(valid, key=lambda c: c[0])
    except Exception:
        return kdd

    best_n, best_e = base_n, base_e

    try:
        # Initial cheap growth: cover vertices, then saturate leftover degree.
        adj = _adjacency(base_n, base_e)
        col = _two_colour(base_n, adj)
        cur_n = _cover_grow(base_n, adj, col, d, D, rng, deadline)
        _augment(cur_n, adj, col, d, rng)
        if cur_n > best_n:
            e = _edge_list(cur_n, adj)
            if lib.is_valid(cur_n, e, d, D):
                best_n, best_e = cur_n, e
        cur_n, cur_adj, cur_col = cur_n, adj, col

        # Annealing growth: add a vertex, repair by swaps, then cover/saturate.
        fails = 0
        while time.monotonic() < deadline and fails < MAX_FAILS:
            res = _attempt(cur_n, cur_adj, cur_col, d, D, rng, deadline)
            if res is None:
                fails += 1
                continue
            fails = 0
            n2, adj2, col2 = res
            n2 = _cover_grow(n2, adj2, col2, d, D, rng, deadline)
            _augment(n2, adj2, col2, d, rng)
            cur_n, cur_adj, cur_col = n2, adj2, col2
            if n2 > best_n:
                e2 = _edge_list(n2, adj2)
                if lib.is_valid(n2, e2, d, D):
                    best_n, best_e = n2, e2
    except Exception:
        pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return kdd
