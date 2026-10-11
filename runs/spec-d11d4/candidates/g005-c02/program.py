import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Group-lift search for D >= 4.
#
# A 2-vertex base graph with d parallel darts (voltages t_1..t_d in a group G)
# lifts to a bipartite graph on 2|G| vertices: a_x ~ b_{x*t} for each t in T.
# Left multiplication by h is an automorphism, transitive on each side, so
# diameter <= D is equivalent to: BFS from a_e and from b_e reaches everything
# within D steps. The defect count is cheap enough to drive a local search on T.
# ----------------------------------------------------------------------------

class _Grp:
    def __init__(self, N, mul, inv):
        self.N = N
        self.mul = mul
        self.inv = inv
        self.cache = {}

    def rm(self, s):
        """Table x -> x*s, built lazily and cached."""
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
    """Non-cyclic semidirect specs (m, k, r) of order N, shuffled; cyclic (None) last."""
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


def _lift_search(d, D, deadline, rng, min_n):
    """Ascending search over group orders N >= min_n; returns (n, edges) of the largest valid lift."""
    hi = lib._moore_bound(d, D) // 2
    best = None
    fails = 0
    N = max(min_n, d + 1)
    while N <= hi and fails < 3 and time.monotonic() < deadline:
        found = None
        for spec in _group_specs(N, rng)[:8]:
            if time.monotonic() >= deadline:
                break
            if spec is None:
                order, mul, inv = lib.cyclic_group(N)
            else:
                order, mul, inv = lib.semidirect_group(*spec)
            g = _Grp(N, mul, inv)
            T = _search_T(g, d, D, rng, 150, deadline)
            if T is not None:
                found = (mul, T)
                break
        if found is not None:
            mul, T = found
            cand = lib.group_lift(2, [(0, 1, t) for t in T], N, mul)
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand
            fails = 0
        else:
            fails += 1
        N += 1
    return best


# ----------------------------------------------------------------------------
# Parent constructions: PG(2,q) for D = 3, and the generalized quadrangle W(q) for D = 4.
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
# Growth by cover: a new vertex on side c joins at most d side-(1-c) vertices
# whose radius-(D-1) balls cover all vertices. Greedy first, then swap local search.
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
            if not cands:
                continue
            chosen = None
            for attempt in range(20):
                if time.monotonic() >= deadline:
                    break
                if attempt < 4:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 1500, deadline)
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


# ----------------------------------------------------------------------------
# Driver. Every candidate is validated with lib.is_valid before it is kept.
# The fallback K_{d,d} is always valid for D >= 2.
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
        # Group-lift search: look only for lifts that beat the current best order.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        min_group_order = best_n // 2 + 1
        res = _lift_search(d, D, start + 0.4 * time_limit, rng, min_group_order)
        if res is not None:
            consider(res[0], res[1])

        # Cover growth from the GQ base and from the best graph so far.
        if gq is not None:
            grow_deadline = start + 0.82 * time_limit
            t = 0
            while time.monotonic() < grow_deadline:
                if t > 0 and rng.random() < 0.5:
                    base_n, base_e = best[0], best[1]
                else:
                    base_n, base_e = gq[0], gq[1]
                n2, e2 = _grow(base_n, base_e, d, D, grow_deadline,
                               random.Random(seed * 131 + t))
                consider(n2, e2)
                t += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
