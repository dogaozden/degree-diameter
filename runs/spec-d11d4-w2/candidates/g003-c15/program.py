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
# Adjacency-list state helpers.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    """Return (adj, color) for a bipartite graph given as an edge list."""
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


def _to_edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _ball(adj, R):
    """Per-vertex bitmasks of all vertices within distance R."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _valid_adj(adj):
    """True if every pair of vertices is within distance 4."""
    full = (1 << len(adj)) - 1
    return all(r == full for r in _ball(adj, 4))


# ----------------------------------------------------------------------------
# NEW: relabel-on-delete vertex removal.
#
# Removing vertex x frees one slot on each neighbour. To keep labels 0..n-1 we
# move the last vertex into slot x. This lets an iterated local search delete
# added vertices and re-grow the graph from the freed slots.
# ----------------------------------------------------------------------------

def _remove_vertex(adj, color, x):
    for s in adj[x]:
        adj[s].remove(x)
    last = len(adj) - 1
    if x != last:
        adj[x] = adj[last]
        for s in adj[x]:
            lst = adj[s]
            lst[lst.index(last)] = x
        color[x] = color[last]
    adj.pop()
    color.pop()


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
#
# A new vertex x on side X joined to S (spare vertices on the opposite side)
# keeps diameter <= 4 iff the union of R3(s), s in S, covers all vertices.
# ----------------------------------------------------------------------------

def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Try to cover all vertices with R3 balls of s0 plus up to d-1 pool vertices; return the set S or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _extend_adj(adj, color, d, deadline, rng, max_fails):
    """Greedily append vertices in place while keeping max degree d and diameter 4."""
    fails = 0
    while fails < max_fails and time.monotonic() < deadline:
        n = len(adj)
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            return
        reach = _ball(adj, 3)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else 0.35
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
            fails += 1
            continue
        x = n
        adj.append(list(S))
        color.append(1 - color[s0])
        for s in S:
            adj[s].append(x)
        fails = 0


# ----------------------------------------------------------------------------
# NEW: remove-and-regrow iterated local search.
#
# Each step deletes one or two added vertices (occasionally a third), re-grows
# with greedy cover extension, and keeps the result only if it is still
# diameter-4 valid and no smaller. Equal-size results are accepted, which lets
# the search drift across plateaus of the vertex-count landscape.
# ----------------------------------------------------------------------------

def _ils(adj, color, d, base, deadline, rng):
    cur_adj, cur_col = adj, color
    best_adj = [list(x) for x in cur_adj]
    best_n = len(best_adj)
    steps = 0
    accepted = 0
    while time.monotonic() < deadline:
        steps += 1
        a = [list(x) for x in cur_adj]
        c = list(cur_col)
        k = 1 + (rng.random() < 0.3) + (rng.random() < 0.1)
        for _ in range(k):
            if len(a) <= 2:
                break
            lo = base if len(a) > base else 0
            x = rng.randrange(lo, len(a))
            _remove_vertex(a, c, x)
        _extend_adj(a, c, d, deadline, rng, 60)
        if len(a) >= len(cur_adj) and _valid_adj(a):
            cur_adj, cur_col = a, c
            accepted += 1
            if len(a) > best_n:
                best_n = len(a)
                best_adj = [list(x) for x in a]
    return best_adj


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 8.0))
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

    # Twin graph on W(d-2), greedy cover extension, then remove-and-regrow search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.5 * budget, rng)
            consider(n2, e2)
            adj, color = _to_adj(n2, e2)
            base = n2
            _extend_adj(adj, color, d, t0 + 0.6 * budget, rng, 4000)
            consider(len(adj), _to_edges(adj))
            try:
                adj2 = _ils(adj, color, d, base, deadline, rng)
                consider(len(adj2), _to_edges(adj2))
            except Exception:
                pass
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
