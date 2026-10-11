import math
import random
import time

import lib

TIME_FRAC = 0.8     # fraction of time_limit used before returning
MARGIN = 2.0        # seconds kept in reserve
ITER = 1000         # annealing steps per growth attempt
MAX_FAILS = 10      # failed growth attempts before resetting to the best graph


# ---------------------------------------------------------------- helpers

def _two_colour(n, adj):
    """Proper 2-colouring of a bipartite graph given as adjacency sets."""
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
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = _balls_adj(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ---------------------------------------------------------------- base constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q+2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg_data(q):
    """Return (m, point_lines, line_points) for PG(2,q); lines are indexed like points."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy S with every line-load and point-load <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """Arc-extended projective plane graphs, one per prime power q with d - q - 1 >= 1."""
    out = []
    for q in range(2, min(d - 2, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, pl, lp = _pg_data(q)
        S = _greedy_arc(m, s, pl, lp, rng, 30, deadline)
        if not S:
            continue
        _, edges = lib.projective_plane_incidence(q)
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ---------------------------------------------------------------- cover growth and saturation

def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within D-1; keeps diameter <= D."""
    if D < 2:
        return n, edges
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _two_colour(n, adj)
    edges = list(edges)
    while time.monotonic() < deadline:
        ball = _balls_adj(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            pool = list(cands)
            covered, chosen = 0, []
            rng.shuffle(pool)
            while covered != full and len(chosen) < d and pool:
                best_i, best_g = -1, 0
                for i, s in enumerate(pool):
                    g = (ball[s] & ~covered).bit_count()
                    if g > best_g:
                        best_i, best_g = i, g
                if best_i < 0:
                    break
                s = pool.pop(best_i)
                chosen.append(s)
                covered |= ball[s]
            if covered == full and chosen:
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices with spare degree (never breaks diameter)."""
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _two_colour(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


# ---------------------------------------------------------------- annealed vertex growth

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


def _augment(n, adj, color, d, rng):
    """Add edges between deficient opposite-colour vertices. Only adds edges, so diameter stays OK."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(d0)
    for u in d0:
        for v in d1:
            if len(adj[u]) >= d:
                break
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)


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
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
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
    budget = deadline - start
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                  # cycle of length 2D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                  # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):    # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    kdd = lib.haar_graph(d, range(d))
    best_n, best_e = kdd[0], kdd[1]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # 1. Record-level constructions.
    if D == 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # 2. Cover extension and edge saturation on the best graph so far.
    n2, e2 = _extend_cover(best_n, list(best_e), d, D, start + 0.3 * budget, rng)
    e2 = _saturate(n2, e2, d, rng)
    consider(n2, e2)

    # 3. Annealed single-vertex growth from the best graph, until the deadline.
    cur_n = best_n
    cur_adj = [set() for _ in range(cur_n)]
    for u, v in best_e:
        cur_adj[u].add(v)
        cur_adj[v].add(u)
    cur_col = _two_colour(cur_n, cur_adj)
    base_state = (cur_n, [set(s) for s in cur_adj], list(cur_col))

    fails = 0
    while time.monotonic() < deadline:
        res = _attempt(cur_n, cur_adj, cur_col, d, D, rng, deadline)
        if res is None:
            fails += 1
            if fails >= MAX_FAILS:
                # Restart from the best valid state seen so far.
                if best_n > cur_n or base_state[0] != cur_n:
                    pass
                cur_n, cur_adj, cur_col = base_state
                fails = 0
            continue
        fails = 0
        cur_n, cur_adj, cur_col = res
        if cur_n > best_n:
            cand_e = _edges(cur_n, cur_adj)
            if lib.is_valid(cur_n, cand_e, d, D):
                best_n, best_e = cur_n, cand_e
                base_state = (cur_n, [set(s) for s in cur_adj], list(cur_col))

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return kdd[0], kdd[1]
