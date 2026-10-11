import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# Returns (n, edges, core) where vertices 0..core-1 are the W(q) incidence graph.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    core = P + L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges, core


# ----------------------------------------------------------------------------
# Shared graph state helpers.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _adjacency_color(n, edges):
    """Return (adj, color): neighbour lists and a 2-colouring (the graph must be bipartite)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    return adj, color


def _ballr(n, adj, r):
    """Return per-vertex bitmasks of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


# ----------------------------------------------------------------------------
# NEW helpers: greedy covers and a two-vertex insertion move.
#
# Single insertion: a new vertex x joined to S (all one colour) needs
#   union of ball3(s) over s in S  ==  all vertices.
#
# Pair insertion (new): add an adjacent pair x-y with colours c and 1-c.
#   x is joined to Sx (colour 1-c), y to Sy (colour c). Every old vertex w
#   must be within 4 of x and of y, which gives the two cover conditions
#       ball3(Sx) | ball2(Sy) == all      (distance from x)
#       ball3(Sy) | ball2(Sx) == all      (distance from y)
#   Each of x, y has degree |S|+1 <= d, so |S| <= d-1. Pair insertion adds
#   two vertices at once, which helps when no single vertex can be attached.
# ----------------------------------------------------------------------------

def _greedy(pool, reach, unc, maxsize, rng):
    """Greedy cover of bitmask unc by reach[v] for v in pool; returns (chosen, remaining uncovered)."""
    chosen = []
    pool = list(pool)
    while unc and len(chosen) < maxsize and pool:
        useful = [v for v in pool if reach[v] & unc]
        if not useful:
            break
        if rng.random() < NOISE:
            bv = rng.choice(useful)
        else:
            bv = max(useful, key=lambda v: (reach[v] & unc).bit_count())
        chosen.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
    return chosen, unc


def _greedy2(pool, r3, r2, unc3, unc2, maxsize, rng):
    """Cover unc3 by r3[v] and unc2 by r2[v] jointly; returns (chosen, rem3, rem2)."""
    chosen = []
    pool = list(pool)
    while (unc3 or unc2) and len(chosen) < maxsize and pool:
        useful = [v for v in pool if (r3[v] & unc3) or (r2[v] & unc2)]
        if not useful:
            break
        if rng.random() < NOISE:
            bv = rng.choice(useful)
        else:
            bv = max(useful, key=lambda v: (r3[v] & unc3).bit_count() + (r2[v] & unc2).bit_count())
        chosen.append(bv)
        unc3 &= ~r3[bv]
        unc2 &= ~r2[bv]
        pool.remove(bv)
    return chosen, unc3, unc2


def _try_single(n, color, r3, d, spare, rng):
    """Try to attach one new vertex; return its neighbour list S or None."""
    full = (1 << n) - 1
    s0 = rng.choice(spare)
    pool = [v for v in spare if color[v] == color[s0] and v != s0]
    chosen, unc = _greedy(pool, r3, full & ~r3[s0], d - 1, rng)
    if unc:
        return None
    return [s0] + chosen


def _try_pair(n, color, r2, r3, d, spare, rng):
    """Try to attach an adjacent pair x-y; return (c, Sx, Sy) or None. x has colour c, y colour 1-c."""
    full = (1 << n) - 1
    c = rng.randrange(2)
    poolX = [v for v in spare if color[v] == 1 - c]
    poolY = [v for v in spare if color[v] == c]
    if not poolX or not poolY:
        return None
    Sy, uy = _greedy(poolY, r3, full, d - 1, rng)
    R2y = 0
    for t in Sy:
        R2y |= r2[t]
    Sx, unc3, uy = _greedy2(poolX, r3, r2, full & ~R2y, uy, d - 1, rng)
    if unc3 or uy:
        return None
    return c, Sx, Sy


def _grow(n, edges, d, deadline, rng, max_fails):
    """Greedily add single vertices and vertex pairs while keeping max degree d and diameter 4.

    Reach tables are recomputed exactly after every insertion, so the result stays valid
    whenever the input graph is valid. Returns (n, edges).
    """
    edges = list(edges)
    adj, color = _adjacency_color(n, edges)
    r3 = _ballr(n, adj, 3)
    r2 = _ballr(n, adj, 2)
    fails = 0
    while fails < max_fails and time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        S = _try_single(n, color, r3, d, spare, rng)
        if S is not None:
            x = n
            n += 1
            edges.extend((s, x) for s in S)
            for s in S:
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[S[0]])
        else:
            res = _try_pair(n, color, r2, r3, d, spare, rng)
            if res is None:
                fails += 1
                continue
            c, Sx, Sy = res
            x = n
            y = n + 1
            n += 2
            edges.append((x, y))
            edges.extend((s, x) for s in Sx)
            edges.extend((t, y) for t in Sy)
            for s in Sx:
                adj[s].append(x)
            for t in Sy:
                adj[t].append(y)
            adj.append([y] + Sx)
            adj.append([x] + Sy)
            color.append(c)
            color.append(1 - c)
        fails = 0
        r3 = _ballr(n, adj, 3)
        r2 = _ballr(n, adj, 2)
    return n, edges


# ----------------------------------------------------------------------------
# Large-neighbourhood search (LNS) for diameter 4.
# ----------------------------------------------------------------------------

LNS_MAX_REMOVE = 3
LNS_FAILS = 300


def _lns(n, edges, core, d, D, deadline, rng, consider):
    """Run LNS until deadline; report every strict improvement through consider(n, edges)."""
    if not lib.is_valid(n, edges, d, D):
        return
    best_n = n
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        room = cur_n - core
        if room < 1:
            break
        k = rng.randint(1, min(LNS_MAX_REMOVE, room))
        R = set(rng.sample(range(core, cur_n), k))
        mp = {}
        for v in range(cur_n):
            if v not in R:
                mp[v] = len(mp)
        base_e = [(mp[u], mp[v]) for u, v in cur_e if u not in R and v not in R]
        sub_deadline = min(deadline, time.monotonic() + 2.0)
        n2, e2 = _grow(len(mp), base_e, d, sub_deadline, rng, LNS_FAILS)
        if n2 < cur_n:
            continue
        if not lib.is_valid(n2, e2, d, D):
            continue
        if n2 > best_n:
            best_n = n2
            consider(n2, e2)
        if n2 > cur_n or rng.random() < 0.5:
            cur_n, cur_e = n2, e2


# ----------------------------------------------------------------------------
# Z_m-voltage lifts of small bipartite base graphs (used when D != 4).
# ----------------------------------------------------------------------------

def _base_adj(k, m, perm, volt):
    """Adjacency of the base dart graph: adj[b] = list of (neighbour_base_id * m, voltage mod m)."""
    adj = [[] for _ in range(2 * k)]
    for i in range(len(perm)):
        pi, vi = perm[i], volt[i]
        for u in range(k):
            v = k + pi[u]
            t = vi[u]
            adj[u].append((v * m, t))
            adj[v].append((u * m, (-t) % m))
    return adj


def _lift_score(k, m, adj, D, limit):
    """Total number of (source, vertex) pairs not reached within D steps; stops early once above limit."""
    N = 2 * k * m
    total = 0
    for b0 in range(2 * k):
        seen = bytearray(N)
        s0 = b0 * m
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                b = x // m
                g = x - b * m
                for bm, t in adj[b]:
                    y = bm + (g + t) % m
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
        if total > limit:
            return total
    return total


def _lift_edges(k, m, adj):
    """Return (n, edges) for the lift described by the base adjacency."""
    E = set()
    for u in range(k):
        for g in range(m):
            x = u * m + g
            for bm, t in adj[u]:
                y = bm + (g + t) % m
                E.add((x, y))
    return 2 * k * m, sorted(E)


def _lift_search(d, D, k, m, deadline, rng):
    """Hill-climb voltages/matchings for a valid lift on 2*k*m vertices; return (n, edges) or None."""

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 400:
            perm, volt = fresh()
            cur = _lift_score(k, m, _base_adj(k, m, perm, volt), D, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(k)
        if rng.random() < 0.6:
            old = volt[i][u]
            volt[i][u] = rng.randrange(m)
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(k)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _lift_score(k, m, _base_adj(k, m, perm, volt), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return _lift_edges(k, m, _base_adj(k, m, perm, volt))


def _lift_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search for lifts of growing order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        ks = [k for k in (2, 3, 4, 5, 6) if 2 * k * (bn // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        m = bn // (2 * k) + 1
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, (deadline - now) / 4.0))
        res = _lift_search(d, D, k, m, slice_end, rng)
        if res is not None:
            n, edges = res
            if n > bn and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                bn = n
    return bn


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2), then exact-cover growth with single and pair insertions.
    start = None
    core = None
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2, core_v = _twin_graph(d - 2, t0 + 0.3 * budget, rng)
            consider(n2, e2)
            n3, e3 = _grow(n2, e2, d, t0 + 0.5 * budget, rng, max_fails=20000)
            consider(n3, e3)
            start = (n3, e3)
            core = core_v
        except Exception:
            start = None
            core = None

    if D == 4:
        if start is None:
            start = best
            core = 0
        try:
            _lns(start[0], start[1], core, d, D, deadline, rng, consider)
        except Exception:
            pass
    elif D >= 2 and d >= 2:
        try:
            _lift_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
