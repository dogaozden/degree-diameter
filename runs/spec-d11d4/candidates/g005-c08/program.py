import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Group-lift search for D >= 4: a 2-vertex base with d parallel darts.
# Left multiplication is transitive on each side, so diameter <= D reduces to
# BFS checks from two sources. Voltages are found by local search.
# ----------------------------------------------------------------------------

class _Grp:
    def __init__(self, N, mul, inv):
        self.N = N
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def rm(self, s):
        r = self.cache.get(s)
        if r is None:
            mul = self.mul
            r = [mul(x, s) for x in range(self.N)]
            self.cache[s] = r
        return r


def _defect(g, T, D):
    """Number of (source, vertex) pairs at distance > D from the two base sources."""
    N = g.N
    Tf = [g.rm(t) for t in T]
    Ti = [g.rm(g.inv(t)) for t in T]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for R in Tf:
                        w = N + R[v]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    y = v - N
                    for R in Ti:
                        w = R[y]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - reached
    return total


def _search_T(g, d, D, rng, steps, deadline):
    N = g.N
    if d > N:
        return None
    T = rng.sample(range(N), d)
    cur = _defect(g, T, D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in T:
            continue
        new = T[:]
        new[i] = cand
        val = _defect(g, new, D)
        if val <= cur or rng.random() < 0.05:
            T, cur = new, val
    return T if cur == 0 else None


def _group_specs(N, rng):
    specs = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    rng.shuffle(specs)
    specs.append(None)
    return specs


def _lift_search(d, D, deadline, rng):
    hi = lib._moore_bound(d, D) // 2
    lo = max(d + 1, int(0.7 * hi))
    best = None
    fails = 0
    N = lo
    while N <= hi and fails < 3 and time.monotonic() < deadline:
        found = None
        specs = _group_specs(N, rng)
        for spec in specs[:6]:
            if time.monotonic() >= deadline:
                break
            if spec is None:
                order, mul, inv = lib.cyclic_group(N)
            else:
                order, mul, inv = lib.semidirect_group(*spec)
            g = _Grp(N, mul, inv)
            T = _search_T(g, d, D, rng, 80, deadline)
            if T is not None:
                found = (mul, T)
                break
        if found is not None:
            mul, T = found
            n_, e_ = lib.group_lift(2, [(0, 1, t) for t in T], N, mul)
            best = (n_, e_)
            fails = 0
        else:
            fails += 1
        N += 1
    return best


# ----------------------------------------------------------------------------
# Constructions: PG(2,q) for D = 3, generalized quadrangle W(q) for D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of W(q): bipartite, diameter 4, degree q+1."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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
            thr = max(1, best_g - 1)
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(40, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _find_cover(cands, ball, full, d, rng, deadline):
    """Try greedy (deterministic, then randomized) and then local search for a cover."""
    if not cands:
        return None
    for attempt in range(4):
        if time.monotonic() >= deadline:
            return None
        c = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if c:
            return c
    for _ in range(4):
        if time.monotonic() >= deadline:
            return None
        c = _cover_ls(cands, ball, full, d, rng, 1500, deadline)
        if c:
            return c
    return None


# ----------------------------------------------------------------------------
# Single-vertex cover extension (parent method).
# ----------------------------------------------------------------------------

def _extend_cover(n, edges, d, D, deadline, rng):
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
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            chosen = _find_cover(cands, ball, full, d, rng, deadline)
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


# ----------------------------------------------------------------------------
# NEW: paired cover extension.
# Each step adds two new vertices u (side 0) and v (side 1) with the edge u-v.
# u's neighbours cover every current vertex within D-1 steps, so u is within D
# of everything. v's neighbours are chosen after u exists and cover the whole
# graph including u, so v is within D of everything too. Adding later vertices
# and edges only shortens distances, so every intermediate graph stays valid.
# Pairing spends the spare degree of u on the u-v edge, which single-vertex
# extension cannot do.
# ----------------------------------------------------------------------------

def _pair_grow(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    misses = 0
    while time.monotonic() < deadline and misses < 4:
        # Cover for u: neighbours on side 1 covering all current vertices.
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        cands_u = [s for s in range(n) if color[s] == 1 and deg[s] < d]
        S = _find_cover(cands_u, ball, full, d, rng, deadline)
        if not S:
            misses += 1
            continue

        u = n
        n += 1
        color.append(0)
        adj.append([])
        deg.append(0)
        for s in S:
            edges.append((s, u))
            adj[s].append(u)
            adj[u].append(s)
            deg[s] += 1
            deg[u] += 1

        # Cover for v: side-0 neighbours covering the whole graph, u included.
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        cands_v = [s for s in range(n) if color[s] == 0 and deg[s] < d and s != u]
        T = _find_cover(cands_v, ball, full, d, rng, deadline)
        if not T or len(T) >= d:
            # u stays in the graph: it is valid and reaches everything, so keep it.
            misses += 1
            continue

        v = n
        n += 1
        color.append(1)
        adj.append([])
        deg.append(0)
        for t in T:
            edges.append((t, v))
            adj[t].append(v)
            adj[v].append(t)
            deg[t] += 1
            deg[v] += 1
        # Pairing edge u-v (u and v are new, so the edge is not a duplicate).
        if deg[u] < d and deg[v] < d:
            edges.append((u, v))
            adj[u].append(v)
            adj[v].append(u)
            deg[u] += 1
            deg[v] += 1
        misses = 0
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Join spare-degree vertices on opposite sides in random order (keeps bipartiteness)."""
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


def _grow_paired(n, edges, d, D, deadline, rng):
    """Paired extension, then single-vertex extension and saturation."""
    n2, e2 = _pair_grow(n, edges, d, D, deadline, rng)
    e2 = _saturate_edges(n2, e2, d, rng)
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver. Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.45 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        # Group-lift search with a 2-vertex base and d darts.
        res = _lift_search(d, D, start + 0.45 * time_limit, rng)
        if res is not None:
            consider(res[0], res[1])

        # GQ base: alternate single-vertex growth and paired growth.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            grow_deadline = start + 0.75 * time_limit
            t = 0
            while time.monotonic() < grow_deadline and t < 40:
                sub_rng = random.Random(seed * 131 + t)
                if t % 2 == 0:
                    n2, e2 = _grow(gq[0], gq[1], d, D, grow_deadline, sub_rng)
                else:
                    n2, e2 = _grow_paired(gq[0], gq[1], d, D, grow_deadline, sub_rng)
                consider(n2, e2)
                t += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
