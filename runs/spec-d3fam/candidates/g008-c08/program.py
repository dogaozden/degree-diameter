import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 1200           # guided-annealing steps per growth attempt
MAX_FAILS = 30        # consecutive failed growth attempts before stopping


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


def _state(n, adj, D):
    """Return (number of bad unordered pairs, list of those pairs as (x, y) with x < y)."""
    reach = _balls_adj(n, adj, D)
    full = (1 << n) - 1
    total = 0
    bad = []
    for x in range(n):
        miss = full & ~reach[x]
        total += miss.bit_count()
        m = miss & ~((1 << (x + 1)) - 1)   # keep only bits y > x
        while m:
            low = m & -m
            bad.append((x, low.bit_length() - 1))
            m ^= low
    return total // 2, bad


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


# ---------------------------------------------------------------- new move: bad-pair-guided rewiring

def _apply(adj, rem, add):
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


def _undo(adj, rem, add):
    for u, v in add:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in rem:
        adj[u].add(v)
        adj[v].add(u)


def _guided_move(adj, color, bad, rng):
    """Rewire around a random bad pair (x, y). Preserves all degrees and bipartiteness.

    Same colour: remove (x,a),(y,b), add (x,b),(y,a).
    Opposite colour: remove (x,a),(y,b), add (x,y),(a,b); this creates the edge x-y that fixes the pair.
    Returns (rem, add) if applied, else None (nothing mutated).
    """
    x, y = bad[rng.randrange(len(bad))]
    if not adj[x] or not adj[y]:
        return None
    a = rng.choice(tuple(adj[x]))
    b = rng.choice(tuple(adj[y]))
    if color[x] == color[y]:
        if a == b or b in adj[x] or a in adj[y]:
            return None
        rem = [(x, a), (y, b)]
        add = [(x, b), (y, a)]
    else:
        if b in adj[a] or x in adj[y] or a == b:
            return None
        rem = [(x, a), (y, b)]
        add = [(x, y), (a, b)]
    _apply(adj, rem, add)
    return rem, add


def _anneal(n, adj, color, D, rng, deadline):
    """Drive the bad-pair count to zero with guided moves. Returns True on success."""
    cost, bad = _state(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            return True
        if time.monotonic() > deadline:
            return False
        if not bad:
            return cost == 0
        mv = _guided_move(adj, color, bad, rng)
        if mv is None:
            continue
        new_cost, new_bad = _state(n, adj, D)
        delta = new_cost - cost
        temp = 1.2 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost, bad = new_cost, new_bad
        else:
            _undo(adj, *mv)
    return cost == 0


# ---------------------------------------------------------------- local moves

def _pick_neighbours(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1-c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls_adj(n, adj, D - 1)
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


def _attempt(n, adj, color, d, D, rng, deadline):
    """Add one vertex, fill spare degree, then guided-anneal back to the diameter bound."""
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

    _augment(n, adj, color, d, rng)
    if not _anneal(n, adj, color, D, rng, deadline):
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
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Starting candidates (all verified with lib.is_valid).
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))  # record construction, degree q+2 = d
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

    # Growth search with bad-pair-guided rewiring.
    color = _two_colour(base_n, base_e)
    adj = [set() for _ in range(base_n)]
    for u, v in base_e:
        adj[u].add(v)
        adj[v].add(u)
    cur_n, cur_adj, cur_col = base_n, adj, color
    best_n, best_e = base_n, base_e

    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _attempt(cur_n, cur_adj, cur_col, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur_n, cur_adj, cur_col = res
        if cur_n > best_n:
            best_n, best_e = cur_n, _edges(cur_n, cur_adj)

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
