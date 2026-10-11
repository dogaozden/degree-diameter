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
# Exact-mask cover extension with remove-one / add-few local search.
#
# State: adjacency sets with an alive flag per slot (dead slots are removed
# vertices), a bipartition colour per slot, the max degree d and the diameter
# target D.
#
# A new vertex x on the side opposite s0, joined to S (all on s0's side), keeps
# diameter <= D exactly when the balls of radius D-1 of S together cover every
# alive vertex. Masks are recomputed exactly after every insertion, so each
# insertion is sound on the graph as it stands.
#
# NEW ROUTINE: _local. It removes one extension vertex x (freeing d slots on
# its neighbours), regrows up to two vertices into the freed capacity, and then
# checks the whole graph with lib.is_valid. A move is kept when at least one
# vertex is added, so the vertex count never decreases. Otherwise the graph is
# restored exactly (new vertices are truncated and x is reattached). This is a
# plateau-walking search that can gain by one vertex per successful double-add.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
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


def _from_edges(n, edges, d, D):
    """Build the mutable state from an edge list, with a BFS two-colouring."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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
    return {"adj": adj, "color": color, "alive": [True] * n, "d": d, "D": D}


def _masks(st):
    """Exact radius-(D-1) balls of all alive vertices, as bitmasks, plus the alive mask."""
    adj, alive = st["adj"], st["alive"]
    R = st["D"] - 1
    N = len(adj)
    reach = [(1 << v) if alive[v] else 0 for v in range(N)]
    for _ in range(R):
        new = [0] * N
        for v in range(N):
            if alive[v]:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
        reach = new
    full = 0
    for v in range(N):
        if alive[v]:
            full |= 1 << v
    return reach, full


def _grow(st, deadline, rng, limit, fail_cap):
    """Add up to `limit` vertices, each covering every alive vertex exactly. Returns the new ids."""
    adj, color, alive, d = st["adj"], st["color"], st["alive"], st["d"]
    added = []
    fails = 0
    reach, full = _masks(st)
    spare = [v for v in range(len(adj)) if alive[v] and len(adj[v]) < d]
    while spare and len(added) < limit and fails < fail_cap and time.monotonic() < deadline:
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = [s0]
        unc = full & ~reach[s0]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)
        if unc:
            fails += 1
            continue
        x = len(adj)
        adj.append(set(S))
        alive.append(True)
        color.append(1 - color[s0])
        for s in S:
            adj[s].add(x)
        added.append(x)
        reach, full = _masks(st)
        spare = [v for v in spare if len(adj[v]) < d]
        if len(S) < d:
            spare.append(x)
        fails = 0
    return added


def _to_edges(st):
    """Compact the alive vertices to 0..m-1 and return (m, edges)."""
    adj, alive = st["adj"], st["alive"]
    idx = {}
    for v in range(len(adj)):
        if alive[v]:
            idx[v] = len(idx)
    edges = [(idx[v], idx[u]) for v in idx for u in adj[v] if v < u]
    return len(idx), edges


def _check(st):
    n, edges = _to_edges(st)
    return lib.is_valid(n, edges, st["d"], st["D"])


def _undo(st, x, N, nb):
    """Truncate vertices added since slot count nb, and reattach removed vertex x with neighbours N."""
    adj, alive, color = st["adj"], st["alive"], st["color"]
    for a in range(nb, len(adj)):
        for s in adj[a]:
            adj[s].discard(a)
    del adj[nb:]
    del alive[nb:]
    del color[nb:]
    alive[x] = True
    adj[x] = set(N)
    for s in N:
        adj[s].add(x)


def _local(st, n0, deadline, rng):
    """Remove-one / add-up-to-two local search over extension vertices (ids >= n0). Never shrinks the graph."""
    adj, alive = st["adj"], st["alive"]
    ext = [v for v in range(n0, len(adj)) if alive[v]]
    while ext and time.monotonic() < deadline:
        x = ext[rng.randrange(len(ext))]
        nb = len(adj)
        N = list(adj[x])
        for s in N:
            adj[s].discard(x)
        adj[x] = set()
        alive[x] = False
        added = _grow(st, deadline, rng, 2, 60)
        if added and _check(st):
            ext.remove(x)
            ext.extend(added)
        else:
            _undo(st, x, N, nb)


def _improve(n, edges, d, D, deadline, rng):
    """Extend a valid graph by exact cover insertions, then run the local search. Returns (n, edges)."""
    st = _from_edges(n, edges, d, D)
    now = time.monotonic()
    _grow(st, now + 0.5 * (deadline - now), rng, 10 ** 9, 3000)
    _local(st, n, deadline, rng)
    return _to_edges(st)


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

    # Twin graph on W(d-2), then exact cover extension and local search.
    start = None
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.4 * budget, rng)
            consider(n2, e2)
            if lib.is_valid(n2, e2, d, D):
                start = (n2, e2)
        except Exception:
            start = None

    if start is None:
        start = best

    if D >= 3:
        try:
            n3, e3 = _improve(start[0], start[1], d, D, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
