import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit).
#   ALG_END   : algebraic bases and cover growth end here.
#   LIFT_END  : group voltage-lift annealing ends here.
#   SA_END    : incremental edge-swap annealing (new in this version) ends here.
# ----------------------------------------------------------------------------
ALG_END = 0.12
LIFT_END = 0.42
SA_END = 0.88
GQ_Q_MAX = 9
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane (D = 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q <= min(d - 1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# A new vertex whose neighbours' radius-(D-1) balls cover everything keeps the
# diameter bound, since old distances only shrink.
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng):
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
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: incremental edge-swap annealing (diameter repair by local moves).
#
# State: n vertices with a fixed 2-colouring `color`, an edge list E of pairs
# (side0, side1), and adjacency sets. Max degree d is maintained as an
# invariant. The objective is the number of vertex pairs at distance > D.
# Three moves:
#   swap  : (u,v),(x,y) -> (u,y),(x,v)          (degrees preserved)
#   shift : (x,y) -> (a,y) with a deficient      (moves a spare slot)
#   add   : join two deficient opposite vertices (never increases the cost)
# Growth adds one vertex per side and repairs with this annealing, warm-started
# from the last valid graph, so each success is a strictly larger valid graph.
# ----------------------------------------------------------------------------

def _ball_cost(n, adjs, D):
    """Number of unordered vertex pairs at distance > D, via bitset balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adjs[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _replace(E, adjs, i, new):
    """Replace edge E[i] by `new`, keeping the adjacency sets in sync."""
    a, b = E[i]
    adjs[a].discard(b)
    adjs[b].discard(a)
    c, e = new
    adjs[c].add(e)
    adjs[e].add(c)
    E[i] = new


def _undo(E, adjs, log):
    """Revert a logged move."""
    for op in reversed(log):
        if op[0] == 'a':
            a, b = op[1], op[2]
            E.pop()
            adjs[a].discard(b)
            adjs[b].discard(a)
        else:
            _replace(E, adjs, op[1], op[2])


def _try_swap(E, adjs, rng):
    m = len(E)
    if m < 2:
        return None
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    u, v = E[i]
    x, y = E[j]
    if u == x or v == y:
        return None
    if y in adjs[u] or v in adjs[x]:
        return None
    log = [('r', i, (u, v)), ('r', j, (x, y))]
    _replace(E, adjs, i, (u, y))
    _replace(E, adjs, j, (x, v))
    return log


def _try_shift(E, adjs, color, n, d, rng):
    if not E:
        return None
    i = rng.randrange(len(E))
    x, y = E[i]
    if rng.random() < 0.5:
        cands = [v for v in range(n)
                 if color[v] == 0 and v != x and len(adjs[v]) < d and v not in adjs[y]]
        if not cands:
            return None
        a = rng.choice(cands)
        log = [('r', i, (x, y))]
        _replace(E, adjs, i, (a, y))
    else:
        cands = [v for v in range(n)
                 if color[v] == 1 and v != y and len(adjs[v]) < d and v not in adjs[x]]
        if not cands:
            return None
        b = rng.choice(cands)
        log = [('r', i, (x, y))]
        _replace(E, adjs, i, (x, b))
    return log


def _try_add(E, adjs, color, n, d, rng):
    d0 = [v for v in range(n) if color[v] == 0 and len(adjs[v]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adjs[v]) < d]
    if not d0 or not d1:
        return None
    a = rng.choice(d0)
    b = rng.choice(d1)
    if b in adjs[a]:
        return None
    E.append((a, b))
    adjs[a].add(b)
    adjs[b].add(a)
    return [('a', a, b)]


def _sa_repair(n, color, E, adjs, d, D, deadline, rng):
    """Anneal edge moves until every pair is within D. Mutates state; True on success."""
    cost = _ball_cost(n, adjs, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T_HI, T_LO = 1.0, 0.08
    T = T_HI
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        if (it & 31) == 0:
            T = T_HI * (T_LO / T_HI) ** min(1.0, (now - t0) / span)
        it += 1
        r = rng.random()
        if r < 0.45:
            log = _try_swap(E, adjs, rng)
        elif r < 0.85:
            log = _try_shift(E, adjs, color, n, d, rng)
        else:
            log = _try_add(E, adjs, color, n, d, rng)
        if log is None:
            continue
        c2 = _ball_cost(n, adjs, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _undo(E, adjs, log)
    return True


def _sa_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex per side and repair by annealing; return the largest valid graph."""
    adjs = [set() for _ in range(n)]
    for u, v in edges:
        adjs[u].add(v)
        adjs[v].add(u)
    color = _bipartition(n, [list(s) for s in adjs])
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    best = (n, list(edges))
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        state = None
        # Two attempts per stage: a shorter one, then one using all remaining time.
        for frac in (0.5, 1.0):
            t = time.monotonic()
            if t >= deadline:
                break
            end = t + frac * (deadline - t)
            c2 = color + [0, 1]
            a2 = [set(s) for s in adjs] + [set(), set()]
            E2 = list(E)
            if _sa_repair(n + 2, c2, E2, a2, d, D, end, rng):
                state = (n + 2, c2, E2, a2)
                break
        if state is None:
            break
        n, color, E, adjs = state
        best = (n, [(a, b) for a, b in E])
    return best


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed (kept from the parent).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    # Algebraic bases and cover growth.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if pg[0] >= moore:
                return best
            consider(_grow(pg[0], pg[1], d, D, start + 0.5 * ALG_END * T, rng))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
            if gq[0] >= moore:
                return best
            consider(_grow(gq[0], gq[1], d, D, start + ALG_END * T, rng))

    # Group voltage lifts (annealed).
    lift_deadline = start + LIFT_END * T
    try:
        ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 2, 2, 3, 4]
        iters = 1500 if D >= 5 else 400
        while time.monotonic() < lift_deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters)
            if res is not None:
                consider(res)
    except Exception:
        pass

    # NEW: incremental edge-swap annealing grows the best valid graph by one
    # vertex per side, repairing diameter by local moves.
    try:
        if best[0] < moore:
            grown = _sa_grow(best[0], best[1], d, D, start + SA_END * T, rng)
            consider(grown)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
