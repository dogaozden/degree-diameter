import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (kept as a safe starting point).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q); degree q + 1, diameter 4."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d, q <= 9 (keeps runtime small)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
    """Greedily add vertices whose neighbourhoods cover all vertices within distance D-1 of the deficient side."""
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with remaining spare degree."""
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
# Twin duplication (non-adjacent twins keep distances and bipartiteness).
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW construction: bipartite voltage lifts over small non-abelian groups.
#
# Base: a bipartite multigraph on a + a vertices, dd-regular (dd = d or d-1),
# built from random stub matchings. Each base dart (u, v) carries a voltage g
# in a group G of order N (a semidirect product Z_m x| Z_k). The lift has
# 2a*N vertices. Voltages on parallel darts are kept distinct, so the lift is
# simple and dd-regular. Hill climbing over voltages minimises the number of
# pairs at distance more than D. When dd = d-1 the lift has spare degree, and
# cover growth plus saturation can add more vertices.
# ----------------------------------------------------------------------------

def _group_choices(N):
    """All (m, k, r) with semidirect_group(m, k, r) of order N = m*k, m >= 2 (r = 1 gives Z_m x Z_k)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_base(a, dd, rng):
    """Random dd-regular bipartite multigraph on sides 0..a-1 (left) and 0..a-1 (right), as (u, v) darts."""
    A = [u for u in range(a) for _ in range(dd)]
    B = [v for v in range(a) for _ in range(dd)]
    rng.shuffle(B)
    return list(zip(A, B))


def _init_voltages(pairs, N, rng):
    used = {}
    volt = []
    for p in pairs:
        s = used.setdefault(p, set())
        g = rng.randrange(N)
        while g in s:
            g = rng.randrange(N)
        s.add(g)
        volt.append(g)
    return volt


def _lift(a, pairs, volt, N, mul):
    darts = [(u, a + v, g) for (u, v), g in zip(pairs, volt)]
    return lib.group_lift(2 * a, darts, N, mul)


def _climb(a, pairs, N, mul, D, rng, deadline, max_iter):
    """Hill climb on voltages minimising bad pairs. Returns (cost, voltages)."""
    volt = _init_voltages(pairs, N, rng)
    n, e = _lift(a, pairs, volt, N, mul)
    cur = lib.bad_pairs(n, e, D)
    it = 0
    while cur > 0 and it < max_iter and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(len(pairs))
        p = pairs[i]
        used = {volt[j] for j in range(len(pairs)) if j != i and pairs[j] == p}
        if len(used) >= N:
            continue
        g = rng.randrange(N)
        while g in used:
            g = rng.randrange(N)
        old = volt[i]
        volt[i] = g
        n, e2 = _lift(a, pairs, volt, N, mul)
        new = lib.bad_pairs(n, e2, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.05):
            cur = new
        else:
            volt[i] = old
    return cur, volt


def _voltage_search(d, D, deadline, rng, consider, best_n):
    """Random restarts of voltage lifts, targeting orders slightly above the current best."""
    if d < 2:
        return
    while time.monotonic() < deadline:
        dd = d if (d - 1 < 1 or rng.random() < 0.6) else d - 1
        a = rng.choice((2, 2, 3))
        lo = best_n() // (2 * a) + 1
        N = rng.randrange(lo, lo + 12)
        if N <= dd:
            continue
        choices = _group_choices(N)
        if not choices:
            continue
        m, k, r = rng.choice(choices)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        pairs = _random_base(a, dd, rng)
        cdl = min(deadline, time.monotonic() + 3.0)
        cur, volt = _climb(a, pairs, order, mul, D, rng, cdl, 2000)
        if cur != 0:
            continue
        n, e = _lift(a, pairs, volt, order, mul)
        consider(n, e)
        if dd < d:
            n2, e2 = _grow(n, e, d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# Redundant-edge pruning and regrowth from the best graph.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Fractions of the usable budget T = 0.85 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, plus twin/cover trials (safety net)
#   B  NEW: voltage lifts over semidirect products, hill-climbed to diameter D
#   C  pruning and regrowth from the best valid graph
# Every candidate passes lib.is_valid before it is kept. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    st = {"n": 2 * d, "e": [(i, d + j) for i in range(d) for j in range(d)]}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, list(e)

    def best_n():
        return st["n"]

    # Phase A: structured base and randomized trials.
    base_n, base_e = st["n"], list(st["e"])
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.12), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.30)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: voltage lifts over non-abelian groups.
    if D >= 2 and time.monotonic() < at(0.80):
        _voltage_search(d, D, at(0.80), rng, consider, best_n)

    # Phase C: prune and regrow from the best valid graph.
    if D >= 2 and time.monotonic() < at(1.0):
        _prune_regrow(st["n"], st["e"], d, D, at(1.0), rng, consider)

    if not lib.is_valid(st["n"], st["e"], d, D):
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return st["n"], list(st["e"])
