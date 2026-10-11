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
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Kill-and-regrow iterated local search on diameter-4 graphs.
#
# State: a graph whose vertices carry an "alive" flag. A killed vertex keeps
# its id but loses all edges, so ids stay stable and snapshots are cheap.
# Growth adds a vertex x on the opposite side of a seed s0, joined to a set S
# of spare-degree vertices that covers every alive vertex within distance 3
# of S, which gives distance <= 4 from x. Killing vertices can break existing
# pairs, so every kill is followed by a full diameter check and is rolled back
# if the graph becomes invalid or if regrowth does not recover the count.
# ----------------------------------------------------------------------------

class _G:
    def __init__(self, n, adj, alive, color):
        self.n = n
        self.adj = adj
        self.alive = alive
        self.color = color


def _g_from(n, edges):
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
    return _G(n, adj, [True] * n, color)


def _copy(g):
    return _G(g.n, [list(a) for a in g.adj], list(g.alive), list(g.color))


def _restore(g, s):
    g.n = s.n
    g.adj = s.adj
    g.alive = s.alive
    g.color = s.color


def _reach(g, steps):
    """Bitmask per vertex of all alive vertices within distance `steps`; dead vertices get 0."""
    reach = [(1 << v) if g.alive[v] else 0 for v in range(g.n)]
    for _ in range(steps):
        new = [0] * g.n
        for v in range(g.n):
            if not g.alive[v]:
                continue
            r = reach[v]
            for u in g.adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _alive_mask(g):
    m = 0
    for v in range(g.n):
        if g.alive[v]:
            m |= 1 << v
    return m


def _valid4(g):
    """True iff every pair of alive vertices is within distance 4."""
    full = _alive_mask(g)
    reach = _reach(g, 4)
    return all(reach[v] == full for v in range(g.n) if g.alive[v])


def _kill(g, x):
    for w in g.adj[x]:
        g.adj[w].remove(x)
    g.adj[x] = []
    g.alive[x] = False


def _add_vertex(g, S, side):
    x = g.n
    g.adj.append(list(S))
    g.alive.append(True)
    g.color.append(side)
    for s in S:
        g.adj[s].append(x)
    g.n += 1
    return x


def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex: best gain, or a random useful one with probability noise."""
    if rng.random() < noise:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g_ = (reach[v] & unc).bit_count()
        if g_ > best:
            best, bv = g_, v
    return bv


def _try_extend(g, d, rng, noise, reach, full):
    spare = [v for v in range(g.n) if g.alive[v] and len(g.adj[v]) < d]
    if not spare:
        return False
    s0 = rng.choice(spare)
    pool = [v for v in spare if g.color[v] == g.color[s0] and v != s0]
    S = [s0]
    unc = full & ~reach[s0]
    while unc and len(S) < d and pool:
        bv = _pick(pool, reach, unc, rng, noise)
        if bv < 0:
            break
        S.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
    if unc:
        return False
    _add_vertex(g, S, 1 - g.color[s0])
    return True


def _grow(g, d, deadline, rng, noise, max_fails):
    """Greedily add vertices while keeping max degree d and diameter 4; return number added."""
    added = 0
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        reach = _reach(g, 3)
        full = _alive_mask(g)
        ok = False
        while time.monotonic() < deadline and fails < max_fails:
            if _try_extend(g, d, rng, noise, reach, full):
                added += 1
                fails = 0
                ok = True
                break
            fails += 1
        if not ok:
            break
    return added


def _ext_count(g, base_n):
    return sum(1 for v in range(base_n, g.n) if g.alive[v])


def _ils(g, base_n, d, deadline, rng):
    """Kill 1-3 extension vertices, regrow, accept if the count does not drop; return best graph seen."""
    best = _copy(g)
    best_cnt = _ext_count(g, base_n)
    while time.monotonic() < deadline:
        ext = [v for v in range(base_n, g.n) if g.alive[v]]
        if not ext:
            break
        before = len(ext)
        snap = _copy(g)
        for x in rng.sample(ext, min(rng.randint(1, 3), len(ext))):
            _kill(g, x)
        if not _valid4(g):
            _restore(g, snap)
            continue
        noise = rng.choice([0.1, 0.25, 0.4])
        _grow(g, d, deadline, rng, noise, 150)
        cnt = _ext_count(g, base_n)
        if cnt >= before:
            if cnt > best_cnt:
                best = _copy(g)
                best_cnt = cnt
        else:
            _restore(g, snap)
    return best


def _to_graph(g):
    edges = [(u, v) for v in range(g.n) if g.alive[v] for u in g.adj[v] if u > v]
    return lib.relabel(edges)


def _pipeline(n, edges, d, deadline, rng):
    """Greedy extension of the base graph followed by kill-and-regrow search until the deadline."""
    base_n = n
    g = _g_from(n, edges)
    now = time.monotonic()
    greedy_end = now + 0.25 * (deadline - now)
    noise = rng.choice([0.1, 0.25, 0.4])
    _grow(g, d, greedy_end, rng, noise, 3000)
    g = _ils(g, base_n, d, deadline, rng)
    return _to_graph(g)


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
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4:
        # Generalized quadrangle W(d-1): degree d, diameter 4.
        if lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Twin graph on W(d-2) (degree d, diameter 4), then kill-and-regrow search.
        if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                now = time.monotonic()
                base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
                consider(*base)
                n2, e2 = _pipeline(base[0], base[1], d, deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
