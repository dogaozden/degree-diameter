import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 1500           # annealing steps per growth attempt
MAX_FAILS = 8         # consecutive failed growth attempts before stopping
RELOC_P = 0.25        # probability that an annealing step is a vertex relocation


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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    reach = _balls_adj(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


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


def _relocate_move(n, adj, color, d, D, rng):
    """Vertex relocation: detach a badly-served vertex and re-attach it greedily.

    Chooses among vertices with unreachable partners (biased to the worst of 3 samples),
    removes all its edges, and reconnects it to d opposite-colour vertices with spare
    degree, chosen greedily to cover radius-(D-1) balls. Degrees stay <= d and the
    graph stays bipartite. Returns (v, old, chosen) for undo, or None.
    """
    reach = _balls_adj(n, adj, D)
    bad = [n - reach[v].bit_count() for v in range(n)]
    cands = [v for v in range(n) if bad[v] > 0]
    if not cands:
        return None
    v = max((rng.choice(cands) for _ in range(3)), key=lambda x: bad[x])
    c = color[v]
    old = list(adj[v])
    for u in old:
        adj[u].discard(v)
    adj[v] = set()
    spare = [u for u in range(n) if color[u] == 1 - c and len(adj[u]) < d]
    if len(spare) < d:
        for u in old:
            adj[u].add(v)
        adj[v] = set(old)
        return None
    balls = _balls_adj(n, adj, D - 1)
    covered, chosen = 0, []
    cand = spare[:]
    rng.shuffle(cand)
    while len(chosen) < d and cand:
        best_u, best_g = cand[0], -1
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    for u in chosen:
        adj[u].add(v)
        adj[v].add(u)
    return v, old, chosen


def _unrelocate(adj, v, old, chosen):
    for u in chosen:
        adj[u].discard(v)
    adj[v] = set(old)
    for u in old:
        adj[u].add(v)


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
    """Add one vertex and anneal until the diameter bound holds again. Returns new state or None."""
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
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if rng.random() < RELOC_P:
            mv = _relocate_move(n, adj, color, d, D, rng)
            if mv is None:
                continue
            new = _bad_pairs(n, adj, D)
            delta = new - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = new
            else:
                _unrelocate(adj, *mv)
        else:
            mv = _swap(adj, side0, rng)
            if mv is None:
                continue
            new = _bad_pairs(n, adj, D)
            delta = new - cost
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

    # Growth search: add vertices with local annealing (swaps + relocations),
    # keep the best valid graph.
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
