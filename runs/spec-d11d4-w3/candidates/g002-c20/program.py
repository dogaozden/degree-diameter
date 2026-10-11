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
    """Return a large independent set of the graph found before deadline."""
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
# Radius-3 balls. A new vertex x joined to S (all on one side, spare degree)
# keeps diameter <= 4 exactly when the union of R3(s), s in S, covers all
# vertices. Adding a vertex never lengthens existing shortest paths, so
# validity of the rest of the graph is preserved.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _colour(n, adj):
    """Two-colour each component (graph is bipartite)."""
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
    return color


def _greedy_cover(s0, spare, reach, color, full, d, rng):
    """Greedy cover of all vertices by R3 balls of same-colour spare vertices starting at s0; return S or None."""
    pool = [v for v in spare if color[v] == color[s0] and v != s0]
    S = [s0]
    unc = full & ~reach[s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best == 0:
            return None
        tied = [pool[i] for i, g in enumerate(gains) if g == best]
        bv = rng.choice(tied)
        S.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
    if unc:
        return None
    return S


def _dfs_cover(pool, reach, full, d, rng, budget):
    """Bounded randomized DFS for a cover of all vertices by R3 balls of pool vertices (at most d).

    Branches on an uncovered vertex with the fewest available coverers. Returns list or None.
    """
    nodes = [0]

    def rec(chosen, unc):
        if unc == 0:
            return chosen
        if len(chosen) >= d or nodes[0] >= budget:
            return None
        nodes[0] += 1
        bits = bin(unc)[:1:-1]
        ones = [i for i, c in enumerate(bits) if c == "1"]
        sample = ones if len(ones) <= 8 else rng.sample(ones, 8)
        best_cov = None
        for u in sample:
            cov = [v for v in pool if (reach[v] >> u) & 1]
            if not cov:
                return None
            if best_cov is None or len(cov) < len(best_cov):
                best_cov = cov
        rng.shuffle(best_cov)
        best_cov.sort(key=lambda v: -(reach[v] & unc).bit_count())
        for v in best_cov[:3]:
            res = rec(chosen + [v], unc & ~reach[v])
            if res is not None:
                return res
        return None

    return rec([], full)


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices (random-tie greedy cover) while keeping max degree d and diameter 4."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _colour(n, adj)

    fails = 0
    while time.monotonic() < deadline and fails < 400:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        cover = None
        for _ in range(12):
            if time.monotonic() >= deadline:
                break
            s0 = rng.choice(spare)
            cover = _greedy_cover(s0, spare, reach, color, full, d, rng)
            if cover is not None:
                break
        if cover is None:
            fails += 1
            continue
        x = n
        n += 1
        for s in cover:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(cover))
        color.append(1 - color[cover[0]])
        fails = 0
    return n, edges


def _extend2(n, edges, d, deadline, rng):
    """Alternative extension: pick a colour class at random, then search for a cover by bounded DFS.

    Explores covers that the greedy chain never reaches. Each new vertex is joined only to
    same-colour spare vertices, so bipartiteness is preserved.
    """
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _colour(n, adj)

    fails = 0
    while time.monotonic() < deadline and fails < 40:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        by = {0: [], 1: []}
        for v in range(n):
            if len(adj[v]) < d:
                by[color[v]].append(v)
        cols = [c for c in (0, 1) if by[c]]
        if not cols:
            break
        cc = rng.choice(cols)
        pool = by[cc]
        cover = None
        for _ in range(4):
            if time.monotonic() >= deadline:
                break
            cover = _dfs_cover(pool, reach, full, d, rng, 400)
            if cover:
                break
        if not cover:
            fails += 1
            continue
        x = n
        n += 1
        for s in cover:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(cover))
        color.append(1 - cc)
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            # Twin base on W(d-2): degree d, diameter 4.
            twin_deadline = t0 + 0.35 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            base = (n2, e2) if lib.is_valid(n2, e2, d, D) else None
            if base is not None:
                consider(n2, e2)
                # Greedy extension (previous strategy) up to a fraction of the budget.
                n3, e3 = _extend(n2, e2, d, t0 + 0.55 * budget, rng)
                consider(n3, e3)
                # New strategy: randomized DFS covers, continued from the best graph so far.
                start = (n3, e3) if lib.is_valid(n3, e3, d, D) else (n2, e2)
                n4, e4 = _extend2(start[0], start[1], d, deadline, rng)
                consider(n4, e4)
                # Also try the DFS strategy from the raw twin base if time remains.
                if time.monotonic() < deadline - 2.0:
                    n5, e5 = _extend2(n2, e2, d, deadline, rng)
                    consider(n5, e5)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
