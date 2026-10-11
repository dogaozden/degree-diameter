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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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
# Greedy set-cover vertex extension for diameter 4.
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# existing vertex. Adding x only shortens distances, so no other pair can break.
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
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

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Iterated local search over set-based graphs (diameter D, max degree d).
#
# State: adj (list of sets), alive (bool per id), color (bipartition side).
# A move removes 1-3 extension vertices, greedily regrows with fresh random
# seeds, and keeps the result only if it is still valid and not smaller.
# ----------------------------------------------------------------------------

def _colors_from_edges(n, edges):
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
    return color


def _alive_mask(alive):
    m = 0
    for v, a in enumerate(alive):
        if a:
            m |= 1 << v
    return m


def _reach(adj, alive, R):
    """Per-vertex bitmask of alive vertices within distance R (dead vertices get 0)."""
    N = len(adj)
    reach = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(R):
        new = reach[:]
        for v in range(N):
            if alive[v]:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
        reach = new
    return reach


def _diam_ok(adj, alive, D):
    reach = _reach(adj, alive, D)
    am = _alive_mask(alive)
    return all(reach[v] == am for v in range(len(adj)) if alive[v])


def _grow(adj, alive, color, d, D, rng, deadline, max_add, max_fail):
    """Greedily attach new vertices (set cover of radius D-1 balls); return number added."""
    added = 0
    fails = 0
    reach = None
    while added < max_add and fails < max_fail and time.monotonic() < deadline:
        if reach is None:
            reach = _reach(adj, alive, D - 1)
        N = len(adj)
        full = _alive_mask(alive)
        spare = [v for v in range(N) if alive[v] and len(adj[v]) < d]
        if not spare:
            break
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = [s0]
        unc = full & ~reach[s0]
        while unc and len(S) < d and pool:
            best_g, bv = 0, -1
            for v in pool:
                g = (reach[v] & unc).bit_count()
                if g > best_g:
                    best_g, bv = g, v
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)
        if unc:
            fails += 1
            continue
        x = N
        adj.append(set(S))
        for s in S:
            adj[s].add(x)
        alive.append(True)
        color.append(1 - color[s0])
        added += 1
        fails = 0
        reach = None
    return added


def _ils(adj, alive, color, base_n, d, D, rng, deadline):
    """Perturb-and-regrow search; return (n, edges) of the best valid graph seen."""

    def snapshot():
        ids = [v for v in range(len(adj)) if alive[v]]
        remap = {v: i for i, v in enumerate(ids)}
        edges = [(remap[v], remap[u]) for v in ids for u in adj[v] if v < u]
        return len(ids), edges

    cur = sum(alive)
    best_n, best_edges = snapshot()
    while time.monotonic() < deadline:
        N = len(adj)
        if not any(alive[v] and len(adj[v]) < d for v in range(N)):
            break
        s_adj = [set(s) for s in adj]
        s_alive = alive[:]
        s_color = color[:]
        ext = [v for v in range(base_n, N) if alive[v]]
        k = rng.randint(1, 3)
        for v in rng.sample(ext, min(k, len(ext))):
            for u in adj[v]:
                adj[u].discard(v)
            adj[v] = set()
            alive[v] = False
        _grow(adj, alive, color, d, D, rng, deadline, max_add=k + 1, max_fail=12)
        if sum(alive) >= cur and _diam_ok(adj, alive, D):
            cur = sum(alive)
            if cur > best_n:
                best_n, best_edges = snapshot()
        else:
            adj[:] = s_adj
            alive[:] = s_alive
            color[:] = s_color
    return best_n, best_edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.3 * budget
    ext_deadline = t0 + 0.6 * budget
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

    # Twin graph on W(d-2), then greedy set-cover extension using the spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, ext_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold stage: iterated local search from the best construction found so far.
    if D >= 4 and time.monotonic() < deadline - 1.0 and best[0] > 0:
        try:
            n0, e0 = best
            color = _colors_from_edges(n0, e0)
            adj = [set() for _ in range(n0)]
            for u, v in e0:
                adj[u].add(v)
                adj[v].add(u)
            alive = [True] * n0
            n_i, e_i = _ils(adj, alive, color, n0, d, D, rng, deadline)
            consider(n_i, e_i)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
