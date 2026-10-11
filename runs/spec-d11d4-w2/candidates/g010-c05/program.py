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
# Mutable graph state: adjacency lists, a side colouring, and an alive flag per
# slot. Killing a vertex frees its neighbours' degree budget without renumbering.
# ----------------------------------------------------------------------------

def _colors(n, adj):
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


def _state_from_edges(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj, _colors(n, adj), [True] * n


def _to_edges(adj, alive):
    """Compact the alive vertices to 0..m-1 and return (m, edges)."""
    idx = {}
    for v in range(len(adj)):
        if alive[v]:
            idx[v] = len(idx)
    edges = [(idx[v], idx[u]) for v in range(len(adj)) if alive[v]
             for u in adj[v] if u > v]
    return len(idx), edges


def _ball(adj, alive, r):
    """Per-slot bitmask of alive vertices within distance r (dead slots get 0)."""
    n = len(adj)
    reach = [(1 << v) if alive[v] else 0 for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            if alive[v]:
                x = reach[v]
                for u in adj[v]:
                    x |= reach[u]
                new[v] = x
        reach = new
    return reach


def _alive_mask(alive):
    m = 0
    for v, a in enumerate(alive):
        if a:
            m |= 1 << v
    return m


def _diam_ok(adj, alive, D):
    r = _ball(adj, alive, D)
    fm = _alive_mask(alive)
    return all(r[v] == fm for v in range(len(adj)) if alive[v])


def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex: best gain, or a random useful one with prob noise."""
    if rng.random() < noise:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _regrow(adj, color, alive, d, deadline, rng, noise):
    """Greedy set-cover extension for diameter 4, in place.

    A new vertex on the opposite side, joined to S (spare-degree vertices on one
    side), keeps diameter <= 4 when the union of 3-balls of S covers every alive vertex.
    """
    while time.monotonic() < deadline:
        reach = _ball(adj, alive, 3)
        fm = _alive_mask(alive)
        spare = [v for v in range(len(adj)) if alive[v] and len(adj[v]) < d]
        if not spare:
            return
        placed = False
        for _ in range(20):
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = fm & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng, noise)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if not unc:
                x = len(adj)
                adj.append(list(S))
                for s in S:
                    adj[s].append(x)
                color.append(1 - color[s0])
                alive.append(True)
                placed = True
                break
        if not placed:
            return


def _ils(adj, color, alive, base_n, d, D, deadline, rng):
    """Iterated local search over extensions: kill 1-3 extension vertices, regrow,
    keep the result if it has at least as many alive vertices and still has diameter D;
    otherwise revert. Returns the best (m, edges) seen."""
    cur = sum(alive)
    best_live = cur
    best = _to_edges(adj, alive)
    while time.monotonic() < deadline:
        s_adj = [list(a) for a in adj]
        s_col = list(color)
        s_al = list(alive)

        ext = [v for v in range(base_n, len(adj)) if alive[v]]
        if ext:
            k = rng.randint(1, 3)
            for x in rng.sample(ext, min(k, len(ext))):
                for u in adj[x]:
                    adj[u].remove(x)
                adj[x] = []
                alive[x] = False

        _regrow(adj, color, alive, d, deadline, rng, rng.choice([0.1, 0.25, 0.4]))

        live = sum(alive)
        if live >= cur and _diam_ok(adj, alive, D):
            cur = live
            if live > best_live:
                best_live = live
                best = _to_edges(adj, alive)
        else:
            adj, color, alive = s_adj, s_col, s_al
    return best


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

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D < 4:
        if not lib.is_valid(best[0], best[1], d, D):
            return 2, [(0, 1)]
        return best

    # Choose a base graph: the twin graph on W(d-2) if available (degree d, diameter 4),
    # otherwise the complete bipartite K_{d,d} (diameter 2).
    base = None
    if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.4 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None
    if base is None:
        base = best

    base_n, base_edges = base
    adj, color, alive = _state_from_edges(base_n, base_edges)

    # Initial greedy extension (a fraction of the remaining time).
    now = time.monotonic()
    grow_end = now + 0.15 * (deadline - now)
    try:
        _regrow(adj, color, alive, d, grow_end, rng, rng.choice([0.1, 0.25, 0.4]))
        consider(*_to_edges(adj, alive))
    except Exception:
        pass

    # Iterated local search on the extension for the rest of the budget.
    try:
        res = _ils(adj, color, alive, base_n, d, D, deadline - 0.5, rng)
        consider(*res)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
