import itertools
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _exact_cover(cands, ball, full, d, budget):
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


def _extend_cover(n, edges, d, D, deadline, rng=None, restarts=200):
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_cover(cands, ball, full, d, 3000)
            if not chosen:
                for attempt in range(restarts):
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


def _grow(n, edges, d, D, deadline, rng, restarts=200):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _legacy_build(d, D, seed, time_limit):
    """The previous construction pipeline, run within its own time budget."""
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    if D >= 4:
        ext_deadline = start + 0.7 * time_limit
        restarts = 600
    else:
        ext_deadline = start + 0.5 * time_limit
        restarts = 200
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

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
            n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng, restarts)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng, restarts)
            consider(n2, e2)

    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# New family: bipartite Cayley (Haar-type) graphs over groups of order N.
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the diameter is checked from just
# one vertex on each side.
# ----------------------------------------------------------------------------

def _group_candidates(N, rng, max_semi=3):
    """Cyclic group of order N plus a few random semidirect products Z_m x| Z_k of order N."""
    cands = []
    _, mul, inv = lib.cyclic_group(N)
    cands.append((mul, inv))
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:max_semi]:
            try:
                _, mul2, inv2 = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            cands.append((mul2, inv2))
    return cands


def _tables(N, mul, inv):
    MT = [[mul(x, y) for y in range(N)] for x in range(N)]
    IV = [inv(x) for x in range(N)]
    return MT, IV


def _cayley_cost(S, MT, IV, N, D):
    """Number of (source, target) pairs unreached within D steps from a_e and from b_e."""
    Sinv = [IV[s] for s in S]
    unreached = 0
    for src in (0, 1):
        sets = [set(), set()]
        sets[src].add(0)
        frontier = {0}
        side = src
        for _ in range(D):
            if not frontier:
                break
            if side == 0:
                nxt = {MT[x][s] for x in frontier for s in S}
            else:
                nxt = {MT[y][t] for y in frontier for t in Sinv}
            nside = 1 - side
            nxt -= sets[nside]
            sets[nside] |= nxt
            frontier = nxt
            side = nside
        unreached += 2 * N - len(sets[0]) - len(sets[1])
    return unreached


def _cayley_hill(N, d, D, MT, IV, rng, iters, deadline):
    """Hill-climb a connection set S of size d in the group so the Cayley graph has diameter <= D."""
    S = rng.sample(range(N), d)
    c = _cayley_cost(S, MT, IV, N, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        cand = rng.randrange(N)
        if cand in S:
            continue
        T = S[:]
        T[rng.randrange(d)] = cand
        ct = _cayley_cost(T, MT, IV, N, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _cayley_search(d, D, rng, n_start, deadline, iters=1500):
    """Find the largest N (from n_start upward) with a valid bipartite Cayley graph of order 2N."""
    best = None
    N = max(n_start, d + 1)
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        found = None
        groups = _group_candidates(N, rng)
        rng.shuffle(groups)
        for mul, inv in groups:
            if time.monotonic() >= deadline:
                break
            MT, IV = _tables(N, mul, inv)
            S = _cayley_hill(N, d, D, MT, IV, rng, iters, deadline)
            if S is not None:
                found = [(x, N + MT[x][s]) for x in range(N) for s in S]
                break
        if found is not None:
            best = (2 * N, found)
            fails = 0
        else:
            fails += 1
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    bold = (D >= 4 and d >= 3)
    legacy_tl = 0.3 * time_limit if bold else 0.85 * time_limit
    lg = _legacy_build(d, D, seed, legacy_tl)
    consider(lg[0], lg[1])

    if bold:
        rng = random.Random(seed + 1)
        n_start = best_n // 2 + 1
        deadline = start + 0.8 * time_limit
        res = _cayley_search(d, D, rng, n_start, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
