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
# Distance-3 balls as bitmasks, and bicolouring.
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


def _bicolor(n, adj):
    """Return a 2-colouring of every vertex (adj: neighbour sequences)."""
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
# NEW: beam cover search.
#
# Plain greedy cover picks the best next cover vertex and commits to it. Here
# the first cover vertex after s0 is chosen from the top-`beam` gains, and each
# choice is completed greedily. The first completion that covers every
# uncovered vertex is used, so different beam branches explore different
# cover sets for the same s0. Each cover set is a valid extension, so no
# validity re-check is needed for vertex additions.
# ----------------------------------------------------------------------------

def _cover(s0, pool, reach, full, d, rng, beam):
    """Return a cover set S (starting with s0) of same-side vertices, or None if no branch covers everything."""
    unc0 = full & ~reach[s0]
    if not unc0:
        return [s0]
    gains = sorted(((reach[v] & unc0).bit_count(), v) for v in pool)
    gains.reverse()
    firsts = [v for g, v in gains[:beam] if g > 0]
    for first in firsts:
        S = [s0, first]
        unc = unc0 & ~reach[first]
        pl = [v for v in pool if v != first]
        while unc and len(S) < d and pl:
            best_g = 0
            ties = []
            for v in pl:
                g = (reach[v] & unc).bit_count()
                if g > best_g:
                    best_g = g
                    ties = [v]
                elif g == best_g and g > 0:
                    ties.append(v)
            if best_g <= 0:
                break
            bv = rng.choice(ties)
            S.append(bv)
            unc &= ~reach[bv]
            pl.remove(bv)
        if not unc:
            return S
    return None


def _extend_beam(n, edges, d, deadline, rng, beam):
    """Add vertices by beam cover search until the deadline; return (n, edges), diameter 4 kept by construction."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bicolor(n, adj)

    MAX_FAILS = 3000
    fails = 0
    reach = None
    dirty = True
    while time.monotonic() < deadline and fails < MAX_FAILS:
        if dirty:
            reach = _ball3(n, adj)
            dirty = False
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = _cover(s0, pool, reach, full, d, rng, beam)
        if S is None:
            fails += 1
            continue
        x = n
        n += 1
        for s in S:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
        dirty = True
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# Edge-split growth ("swap-grow"), with the vertex-cover step using _cover.
# Each move deletes one edge and inserts a vertex, and is checked with
# lib.is_valid, reverting on failure.
# ----------------------------------------------------------------------------

def _pick(pool, reach, unc, rng):
    """Choose a useful cover vertex from pool at random."""
    useful = [v for v in pool if reach[v] & unc]
    if useful:
        return rng.choice(useful)
    return -1


def _swap_grow(n, edges, d, D, deadline, rng):
    """Grow by edge-split moves until the deadline; return (n, edges), always valid."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, [sorted(s) for s in adj])

    while time.monotonic() < deadline:
        sat = [v for v in range(n) if len(adj[v]) == d]
        if not sat:
            break
        s = rng.choice(sat)
        t = rng.choice(sorted(adj[s]))
        key = (s, t) if s < t else (t, s)
        eset.discard(key)
        adj[s].discard(t)
        adj[t].discard(s)

        reach = _ball3([sorted(a) for a in adj] and n, [sorted(a) for a in adj]) \
            if False else _ball3(n, [sorted(a) for a in adj])
        unc = ((1 << n) - 1) & ~reach[s]
        pool = [v for v in range(n) if color[v] == color[s] and v != s and len(adj[v]) < d]
        S = [s]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)

        if unc == 0:
            x = n
            adj.append(set())
            color.append(color[t])
            for w in S:
                adj[w].add(x)
                adj[x].add(w)
                eset.add((w, x))
            if lib.is_valid(n + 1, list(eset), d, D):
                n += 1
                continue
            for w in S:
                adj[w].discard(x)
                eset.discard((w, x))
            adj.pop()
            color.pop()

        adj[s].add(t)
        adj[t].add(s)
        eset.add(key)
    return n, sorted(eset)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.4 * budget
    extend_deadline = t0 + 0.65 * budget
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

    # Twin graph on W(d-2), then restarted beam cover extension, then edge-split growth.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            ext = (n2, e2)
            while time.monotonic() < extend_deadline:
                sub = min(extend_deadline, time.monotonic() + 8.0)
                n3, e3 = _extend_beam(n2, e2, d, sub, rng, beam=4)
                if n3 > ext[0]:
                    ext = (n3, e3)
            consider(*ext)
            n4, e4 = _swap_grow(ext[0], ext[1], d, D, deadline, rng)
            consider(n4, e4)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
