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
# Bitmask balls and the diameter-4 test.
# ----------------------------------------------------------------------------

def _ball(n, adj, r):
    """Per-vertex bitmasks of all vertices within distance r. adj: sets or lists."""
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


def _diam4_ok(n, adj):
    """True iff the graph given by set-adjacency has diameter <= 4 (connected included)."""
    full = (1 << n) - 1
    return all(x == full for x in _ball(n, adj, 4))


def _two_color(n, adj):
    """Proper 2-colouring by BFS (the graph is bipartite)."""
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


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4 (in place, set adjacency).
#
# A new vertex x on side X, joined to a set S of spare-degree vertices on the
# opposite side, keeps diameter <= 4 when the union of R3(s), s in S, covers
# all existing vertices. Balls are recomputed after each success.
# ----------------------------------------------------------------------------

def _grow(adj, color, d, deadline, rng, fail_limit):
    """Add vertices greedily to adj/color in place; return the number added."""
    added = 0
    fails = 0
    while time.monotonic() < deadline and fails < fail_limit:
        n = len(adj)
        reach = _ball(n, adj, 3)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        grown = False
        while time.monotonic() < deadline and fails < fail_limit:
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bestg, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > bestg:
                        bestg, bv = g, v
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            for s in S:
                adj[s].add(x)
            adj.append(set(S))
            color.append(1 - color[s0])
            added += 1
            fails = 0
            grown = True
            break
        if not grown:
            break
    return added


# ----------------------------------------------------------------------------
# NEW: destroy-and-repair local search.
#
# Repeatedly delete one random extension vertex (the freed neighbours get spare
# degree), regrow greedily from the freed slots, and keep the result if it still
# has diameter <= 4 and at least as many vertices. Otherwise restore the saved
# state. Plateau moves (equal size) let the search drift across covers, and the
# best size seen is returned.
# ----------------------------------------------------------------------------

def _remove_vertex(adj, color, x):
    """Delete vertex x from set-adjacency, moving the last vertex into slot x."""
    for u in adj[x]:
        adj[u].discard(x)
    last = len(adj) - 1
    if x != last:
        for u in adj[last]:
            adj[u].discard(last)
            adj[u].add(x)
        adj[x] = adj[last]
        color[x] = color[last]
    adj.pop()
    color.pop()


def _destroy_repair(adj, color, base_n, d, deadline, rng):
    """Local search over extension vertices; return the best adjacency found."""
    best_n = len(adj)
    best_adj = [set(s) for s in adj]
    while time.monotonic() < deadline and len(adj) > base_n:
        n0 = len(adj)
        saved_adj = [set(s) for s in adj]
        saved_color = list(color)
        x = rng.randrange(base_n, n0)
        _remove_vertex(adj, color, x)
        _grow(adj, color, d, deadline, rng, 300)
        if len(adj) >= n0 and _diam4_ok(len(adj), adj):
            if len(adj) > best_n:
                best_n = len(adj)
                best_adj = [set(s) for s in adj]
        else:
            adj[:] = saved_adj
            color[:] = saved_color
    return best_adj


def _to_edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


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

    # Twin graph on W(d-2), greedy extension, then destroy-and-repair search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.4 * budget, rng)
            consider(n2, e2)
            adj = [set() for _ in range(n2)]
            for u, v in e2:
                adj[u].add(v)
                adj[v].add(u)
            color = _two_color(n2, adj)
            _grow(adj, color, d, t0 + 0.55 * budget, rng, 3000)
            consider(len(adj), _to_edges(adj))
            improved = _destroy_repair(adj, color, n2, d, deadline, rng)
            consider(len(improved), _to_edges(improved))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
