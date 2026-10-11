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
#
# Each W(q) vertex has one spare degree slot. We add point twins (adjacent to
# all lines through a point of an independent set I) and line twins (adjacent
# to all points of a set J of pairwise disjoint lines). Returns side labels:
# 0 = point-type vertex, 1 = line-type vertex.
# ----------------------------------------------------------------------------

def _twin_graph(P, lines, deadline, rng):
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
    side = [0] * P + [1] * L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        side.append(0)
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        side.append(1)
        n += 1
    return n, edges, side


# ----------------------------------------------------------------------------
# Greedy growth by dominating new vertices (bold, different-from-parent idea).
#
# Adding a vertex z never increases any existing distance, so z only needs to
# reach every vertex within D. z reaches x within D iff x lies within D-1 of
# some neighbour of z in the current graph. We therefore pick up to d free
# opposite-side vertices whose radius-(D-1) balls cover everything (greedy set
# cover with random tie-breaks), and insert z. Validity is exact by
# construction; the final lib.is_valid check guards anyway.
# ----------------------------------------------------------------------------

def _balls_adj(adj, n, R):
    """Bitmask of vertices within distance R of each vertex, from adjacency lists."""
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


def _grow(n, edges, side, d, R, deadline, rng, trials=6):
    """Greedily insert new vertices that reach everything within R+1; return (n, edges, side)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = list(side)
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        s = rng.randint(0, 1)
        ball = _balls_adj(adj, n, R)
        full = (1 << n) - 1
        free = [u for u in range(n) if side[u] != s and len(adj[u]) < d]
        chosen = None
        for _ in range(trials):
            if time.monotonic() > deadline:
                break
            cover = 0
            pick = []
            avail = list(free)
            while cover != full and len(pick) < d and avail:
                best_u = None
                best_key = None
                for u in avail:
                    g = (ball[u] & ~cover).bit_count()
                    if g == 0:
                        continue
                    key = (g, rng.random())
                    if best_key is None or key > best_key:
                        best_key = key
                        best_u = u
                if best_u is None:
                    break
                pick.append(best_u)
                cover |= ball[best_u]
                avail.remove(best_u)
            if cover == full:
                chosen = pick
                break
        if chosen is None:
            fails += 1
            continue
        fails = 0
        z = n
        n += 1
        side.append(s)
        adj.append(list(chosen))
        for u in chosen:
            adj[u].append(z)
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out, side


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
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

    # W(q) with q = d-2 has one spare slot per vertex: use it.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        try:
            P, lines = _gq_w(q)
            L = len(lines)
            base_edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            base_n = P + L
            base_side = [0] * P + [1] * L

            # (1) Bold: greedy dominating-vertex growth directly from the bare W(q).
            try:
                n1, e1, _ = _grow(base_n, base_edges, base_side, d, D - 1,
                                  t0 + 0.25 * budget, rng)
                consider(n1, e1)
            except Exception:
                pass

            # (2) Parent's twin construction (proven baseline).
            n2, e2, s2 = _twin_graph(P, lines, t0 + 0.6 * budget, rng)
            consider(n2, e2)

            # (3) Continue greedy growth from the twin graph with leftover time.
            try:
                n3, e3, _ = _grow(n2, e2, s2, d, D - 1, deadline, rng)
                consider(n3, e3)
            except Exception:
                pass
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
