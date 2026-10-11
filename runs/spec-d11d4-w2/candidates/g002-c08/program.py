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
# Mutable graph state helpers.
#
# A state is (adj, alive, color): adj[v] is a set of neighbours, alive[v] marks
# live vertices, color[v] is the side of a bipartition. Deleted vertices keep
# their index with an empty neighbour set, so they never affect distances.
# ----------------------------------------------------------------------------

def _adj_from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _two_color(adj):
    N = len(adj)
    color = [-1] * N
    for s in range(N):
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


def _reach_all(adj, k):
    """Per-vertex bitmask of all vertices within distance k (dead vertices reach only themselves)."""
    N = len(adj)
    reach = [1 << v for v in range(N)]
    for _ in range(k):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _alive_mask(alive):
    m = 0
    for v, a in enumerate(alive):
        if a:
            m |= 1 << v
    return m


def _valid(adj, alive, D):
    """Exact check: every live pair within distance D."""
    reach = _reach_all(adj, D)
    full = _alive_mask(alive)
    return all(reach[v] == full for v in range(len(adj)) if alive[v])


def _remove_vertex(adj, alive, x):
    nb = adj[x]
    for s in nb:
        adj[s].discard(x)
    adj[x] = set()
    alive[x] = False
    return nb


def _restore_vertex(adj, alive, x, nb):
    alive[x] = True
    adj[x] = set(nb)
    for s in nb:
        adj[s].add(x)


def _snap(adj, alive, color):
    return [set(s) for s in adj], list(alive), list(color)


def _export(adj, alive):
    idx = {}
    for v in range(len(adj)):
        if alive[v]:
            idx[v] = len(idx)
    edges = []
    for v in range(len(adj)):
        if alive[v]:
            for w in adj[v]:
                if w > v:
                    edges.append((idx[v], idx[w]))
    return len(idx), edges


# ----------------------------------------------------------------------------
# Exact-cover vertex extension for diameter 4.
#
# A new vertex x on side X, joined to a set S of spare-degree vertices on the
# opposite side, keeps diameter <= 4 exactly when the union of R3(s) over s in S
# covers every live vertex. Ball bitmasks are recomputed exactly after every
# addition, so every accepted cover is checked against the current graph.
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


def _grow(adj, alive, color, d, deadline, rng, max_fail):
    """Greedily add vertices while keeping max degree d and diameter 4. Returns the number added."""
    added = 0
    fails = 0
    reach = _reach_all(adj, 3)
    while time.monotonic() < deadline and fails < max_fail:
        N = len(adj)
        spare = [v for v in range(N) if alive[v] and len(adj[v]) < d]
        if not spare:
            break
        full = _alive_mask(alive)
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0] and v != s0]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else 0.35
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
            fails += 1
            continue
        x = N
        adj.append(set(S))
        alive.append(True)
        color.append(1 - color[s0])
        for s in S:
            adj[s].add(x)
        reach = _reach_all(adj, 3)
        added += 1
        fails = 0
    return added


# ----------------------------------------------------------------------------
# Plateau search: delete one added vertex, keep the deletion only if the graph
# stays valid, then refill with greedy extension. Accept equal-size moves and
# return to the best snapshot if the size drops too far.
# ----------------------------------------------------------------------------

def _plateau(adj, alive, color, d, D, base_n, deadline, rng):
    best_adj, best_alive, best_color = _snap(adj, alive, color)
    best_cnt = sum(best_alive)
    cur = best_cnt
    while time.monotonic() < deadline:
        added = [v for v in range(base_n, len(adj)) if alive[v]]
        if not added:
            break
        x = rng.choice(added)
        nb = _remove_vertex(adj, alive, x)
        if not _valid(adj, alive, D):
            _restore_vertex(adj, alive, x, nb)
            continue
        _grow(adj, alive, color, d, min(deadline, time.monotonic() + 0.5), rng, max_fail=8)
        cur = sum(alive)
        if cur > best_cnt:
            best_adj, best_alive, best_color = _snap(adj, alive, color)
            best_cnt = cur
        elif cur < best_cnt - 2:
            adj[:] = [set(s) for s in best_adj]
            alive[:] = list(best_alive)
            color[:] = list(best_color)
            cur = best_cnt
    adj[:] = [set(s) for s in best_adj]
    alive[:] = list(best_alive)
    color[:] = list(best_color)


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

    # Twin graph on W(d-2), then exact-cover extension and plateau search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.35 * budget, rng)
            consider(n2, e2)
            adj = _adj_from_edges(n2, e2)
            alive = [True] * n2
            color = _two_color(adj)
            base_n = n2
            _grow(adj, alive, color, d, t0 + 0.7 * budget, rng, max_fail=4000)
            consider(*_export(adj, alive))
            _plateau(adj, alive, color, d, D, base_n, deadline, rng)
            consider(*_export(adj, alive))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
