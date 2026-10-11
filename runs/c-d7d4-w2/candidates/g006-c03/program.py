import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (kept from the parent).
# ----------------------------------------------------------------------------

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
    """Generalized quadrangle incidence graph W(q), largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers for growing a valid graph by cover vertices and saturation.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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
    """Add vertices whose neighbourhoods cover all vertices within D-1 steps (keeps diameter D)."""
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
    """Join deficient opposite-side vertices (keeps bipartite, degrees <= d, diameter only shrinks)."""
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
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
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
# New construction: voltage lifts over small non-abelian groups.
#
# A base bipartite multigraph has s "A" vertices and t "B" vertices. For each
# pair (i, j) there is a set S_ij of group elements (the voltages), with
# |S_ij| = c_ij and row/column sums of c at most d. The group G (order N) is
# Z_m x|_r Z_k. The lift has vertices (i, x) and (j, y) for x, y in G, and edges
#     (i, x) -- (s + j, x*g)    for g in S_ij.
# Left multiplication by G is an automorphism that acts regularly on each side,
# so the lift has diameter <= D iff every one of the s+t block representatives
# reaches all vertices within D steps. The cost is the total number of
# unreached vertices from those representatives, so cost 0 means valid.
# Voltages are annealed to reduce this cost. Lift orders are (s+t)*N.
# ----------------------------------------------------------------------------

SHAPES = [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]


def _shape(d, s, t, rng):
    """Random s x t count matrix with row and column sums <= d, saturated greedily."""
    c = [[0] * t for _ in range(s)]
    rows = [0] * s
    cols = [0] * t
    cells = [(i, j) for i in range(s) for j in range(t)]
    while True:
        elig = [(i, j) for i, j in cells if rows[i] < d and cols[j] < d]
        if not elig:
            break
        i, j = rng.choice(elig)
        c[i][j] += 1
        rows[i] += 1
        cols[j] += 1
    return c


def _groups(N):
    """All (m, k, r) with Z_m x|_r Z_k of order N = m*k (r = 1 gives the cyclic group)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_cost(s, t, N, mt, S, D):
    """Total unreached vertices (beyond distance D) from the s+t block representatives."""
    n = (s + t) * N
    adj = [[] for _ in range(n)]
    for i in range(s):
        for j in range(t):
            bb = (s + j) * N
            for g in S[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = bb + mt[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    reps = [i * N for i in range(s)] + [(s + j) * N for j in range(t)]
    total = 0
    for r0 in reps:
        seen = bytearray(n)
        seen[r0] = 1
        frontier = [r0]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - cnt
    return total


def _anneal_lift(s, t, c, N, mt, D, deadline, rng):
    """Anneal voltages to cost 0. Returns the voltage sets S on success, else None."""
    cells = [(i, j, c[i][j]) for i in range(s) for j in range(t) if c[i][j] > 0]
    S = [[[] for _ in range(t)] for _ in range(s)]
    for i, j, k in cells:
        S[i][j] = rng.sample(range(N), k)
    cur = _lift_cost(s, t, N, mt, S, D)
    while cur > 0 and time.monotonic() < deadline:
        i, j, k = rng.choice(cells)
        lst = S[i][j]
        idx = rng.randrange(k)
        old = lst[idx]
        cand = rng.randrange(N)
        tries = 0
        while cand in lst and tries < 10 * N:
            cand = rng.randrange(N)
            tries += 1
        if cand in lst:
            continue
        lst[idx] = cand
        new = _lift_cost(s, t, N, mt, S, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / 0.5):
            cur = new
        else:
            lst[idx] = old
    return S if cur == 0 else None


def _lift_edges(s, t, N, mt, S):
    edges = []
    for i in range(s):
        for j in range(t):
            bb = (s + j) * N
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, bb + mt[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2 (and optimal for D = 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, list(best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base (parent's), kept as a strong starting point.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Already at the Moore bound: nothing to improve.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Main stage: voltage lifts over semidirect groups, each attempt targeting
    # a graph strictly larger than the current best.
    per_attempt = max(1.0, 0.07 * time_limit)
    while time.monotonic() < deadline - 0.5:
        s, t = rng.choice(SHAPES)
        N = best_n // (s + t) + 1 + rng.choice((0, 0, 1))
        if N <= d:
            continue
        groups = _groups(N)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        order, mul, _ = lib.semidirect_group(m, k, r)
        if order != N:
            continue
        c = _shape(d, s, t, rng)
        if sum(map(sum, c)) == 0:
            continue
        mt = [[mul(x, y) for y in range(N)] for x in range(N)]
        att_end = min(deadline, time.monotonic() + per_attempt)
        S = _anneal_lift(s, t, c, N, mt, D, att_end, rng)
        if S is None:
            continue
        n = (s + t) * N
        e = _lift_edges(s, t, N, mt, S)
        consider(n, e)
        # Cover growth and saturation on the lift, bounded by the deadline.
        grow_end = min(deadline, time.monotonic() + 2.0)
        n2, e2 = _grow(n, e, d, D, grow_end, rng)
        consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
