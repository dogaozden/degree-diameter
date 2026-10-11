import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4, degree q + 1).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups (new main family).
#
# Group G (order g), connection set S of size d.
# Vertices: A_x = x, B_y = g + y.  Edge A_x -- B_{x*s} for s in S.
# Left multiplication by any h is an automorphism, so the graph is
# vertex-transitive on each side. Diameter <= D holds iff a BFS from A_e and
# from B_e reaches every vertex within D steps. This makes the cost cheap.
# ----------------------------------------------------------------------------

def _make_group(G, rng):
    """Random group of order G: cyclic, or Z_m x| Z_k2 with random action."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, inv = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul, inv


def _tables(G, mul, inv):
    T = [[mul(x, s) for s in range(G)] for x in range(G)]
    I = [inv(s) for s in range(G)]
    return T, I


def _bc_cost(G, T, I, S, D, limit):
    """Unreached (source, vertex) pairs from A_e and B_e within D steps.

    Returns early once the running total exceeds `limit`.
    """
    N = 2 * G
    Iset = [I[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for si in Iset:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
        if total > limit:
            return total
    return total


def _bc_search(d, D, G, rng, deadline, iters):
    """Anneal a connection set S of size d in a random group of order G."""
    mg = _make_group(G, rng)
    if mg is None:
        return None
    _, mul, inv = mg
    T, I = _tables(G, mul, inv)
    S = rng.sample(range(G), d)
    cost = _bc_cost(G, T, I, S, D, float("inf"))
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        Tmp = 2.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - Tmp * math.log(u)
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        old = S[i]
        S[i] = t
        c2 = _bc_cost(G, T, I, S, D, limit)
        if c2 <= limit:
            cost = c2
        else:
            S[i] = old
    if cost == 0:
        return S, T
    return None


def _bc_edges(G, T, S):
    E = []
    for x in range(G):
        row = T[x]
        for s in S:
            E.append((x, G + row[s]))
    return 2 * G, E


# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    end = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured bases.
    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * budget, rng)
            consider(n2, e2)

    if D >= 4:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)]
        if qs:
            gn, ge = _gq_w(qs[0])
            consider(gn, ge)
            gq_deadline = start + 0.3 * budget
            restart = 0
            while time.monotonic() < gq_deadline:
                src = best if restart > 0 and rng.random() < 0.5 else (gn, ge)
                n2, e2 = _grow(src[0], src[1], d, D, gq_deadline, rng,
                               always_random=restart > 0)
                consider(n2, e2)
                restart += 1

    # Main family: bi-Cayley graphs over small groups, annealed connection sets.
    while time.monotonic() < end:
        G0 = max(d, best_n // 2 + 1)
        G = G0 + rng.randrange(0, 12)
        res = _bc_search(d, D, G, rng, end, 1500)
        if res is not None:
            S, T = res
            n, e = _bc_edges(G, T, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
