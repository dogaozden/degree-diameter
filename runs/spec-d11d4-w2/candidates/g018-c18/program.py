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
# Bipartition and distance helpers.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Return a 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[w] == color[u]:
                    return None
    return color


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3 (exact, full recomputation)."""
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


def _ball_bfs(adj, v, r):
    """Exact bitmask of all vertices within distance r of v, by BFS on the current adjacency.

    Used to give a freshly added vertex an exact reach mask without recomputing every vertex.
    """
    mask = 1 << v
    seen = {v}
    frontier = [v]
    for _ in range(r):
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
                    mask |= 1 << w
        frontier = nxt
    return mask


# ----------------------------------------------------------------------------
# Incremental cover-extension with stale-under-approximated reach masks.
#
# A new vertex x on side X, joined to S on the opposite side, keeps diameter
# <= 4 when the union of ball3(s) over s in S covers every existing vertex.
# Reach masks only ever grow as vertices are added, so a stale mask is a
# subset of the true ball: covering with stale masks is still sound.
# ----------------------------------------------------------------------------

def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob noise."""
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


def _state(n0, edges0, bcolor, ext):
    """Rebuild adjacency and colours for base graph plus extension list ext (each entry: S, joined to new vertex)."""
    n = n0 + len(ext)
    adj = [[] for _ in range(n)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    color = list(bcolor)
    for i, S in enumerate(ext):
        x = n0 + i
        color.append(1 - color[S[0]])
        for s in S:
            adj[s].append(x)
            adj[x].append(s)
    return n, adj, color


def _materialize(n0, edges0, ext):
    """Return (n, edges) for base graph plus extension list ext."""
    edges = list(edges0)
    for i, S in enumerate(ext):
        x = n0 + i
        for s in S:
            edges.append((s, x))
    return n0 + len(ext), edges


def _grow(n0, edges0, bcolor, ext, d, deadline, rng, noise, max_fails):
    """Greedily append cover-extension vertices to ext (mutated and returned) until stuck or out of time."""
    n, adj, color = _state(n0, edges0, bcolor, ext)
    reach = _ball3(n, adj)
    full = (1 << n) - 1
    fails = 0
    since = 0
    while fails < max_fails and time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
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
            fails += 1
            continue
        x = n
        n += 1
        full = (full << 1) | 1
        for s in S:
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
        ext.append(S)
        reach.append(_ball_bfs(adj, x, 3))
        fails = 0
        since += 1
        if since >= 8:
            reach = _ball3(n, adj)
            since = 0
    return ext


def _ils(n0, edges0, bcolor, ext, d, deadline, rng):
    """Iterated local search over extensions: roll back the last k added vertices, regrow with fresh noise.

    Rolling back a suffix of the extension list restores an earlier valid graph exactly,
    so every intermediate state is valid by construction.
    """
    cur = list(ext)
    best = list(ext)
    while time.monotonic() < deadline:
        cand = list(cur)
        if cand:
            k = rng.randint(1, min(len(cand), 6))
            del cand[len(cand) - k:]
        slice_end = min(deadline, time.monotonic() + 1.5)
        noise = rng.choice([0.1, 0.25, 0.4, 0.6])
        cand = _grow(n0, edges0, bcolor, cand, d, slice_end, rng, noise, 600)
        if len(cand) >= len(cur) or rng.random() < 0.02:
            cur = cand
        if len(cand) > len(best):
            best = list(cand)
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

    # Twin graph on W(d-2) (degree d), then cover-extension, then iterated local search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(q, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None:
            try:
                n0, edges0 = base
                bcolor = _colors(n0, edges0)
                if bcolor is not None:
                    now = time.monotonic()
                    remaining = deadline - now
                    ext = _grow(n0, edges0, bcolor, [], d,
                                now + 0.15 * remaining, rng, 0.1, 20000)
                    consider(*_materialize(n0, edges0, ext))
                    ext = _ils(n0, edges0, bcolor, ext, d, deadline, rng)
                    consider(*_materialize(n0, edges0, ext))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
