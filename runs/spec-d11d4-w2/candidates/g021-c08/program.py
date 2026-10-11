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
# Ball bitmasks for diameter-4 extension.
#
# B2[v] / B3[v] = vertices within distance 2 / 3 of v (as bitmasks).
# ----------------------------------------------------------------------------

def _step(reach, adj):
    """One round of bitmask neighbourhood expansion."""
    out = []
    for v in range(len(reach)):
        r = reach[v]
        for u in adj[v]:
            r |= reach[u]
        out.append(r)
    return out


def _balls23(n, adj):
    """Return (B2, B3): per-vertex bitmasks of vertices within distance 2 and within distance 3."""
    reach = [1 << v for v in range(n)]
    reach = _step(_step(reach, adj), adj)[:n] if False else _step(reach, adj)
    reach = _step(reach, adj)
    B2 = reach
    B3 = _step(B2, adj)
    return B2, B3


# ----------------------------------------------------------------------------
# Single-vertex greedy set cover (the parent's extension move).
#
# A new vertex x joined to a set S of opposite-side spare vertices keeps
# diameter <= 4 iff the union of B3(s) over s in S covers every existing vertex.
# ----------------------------------------------------------------------------

def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using B3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
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


# ----------------------------------------------------------------------------
# NEW: joint pair extension.
#
# Add two adjacent new vertices x (colour c) and y (colour 1-c). x joins a set
# S of spare colour-(1-c) vertices and y joins a set T of spare colour-c
# vertices. Distances from the new vertices to every old vertex w are:
#   d(x, w) <= 4  iff  w in B3(S) u B2(T)
#   d(y, w) <= 4  iff  w in B2(S) u B3(T)
# (old-old distances can only shrink). So one greedy pass can cover both
# new vertices at once, and it can place vertices that single-vertex covers
# cannot reach because the partner edge supplies extra routes.
# ----------------------------------------------------------------------------

def _pair_attempt(poolA, poolB, B2, B3, full, d, rng, noise):
    """Greedy joint choice of (S, T) covering all old vertices from both x and y; return (S, T) or None.

    poolA: spare vertices of colour c (candidates for T, neighbours of y).
    poolB: spare vertices of colour 1-c (candidates for S, neighbours of x).
    """
    ux = full
    uy = full
    S = []
    T = []
    cA = list(poolA)
    cB = list(poolB)
    while ux or uy:
        if len(S) >= d - 1 and len(T) >= d - 1:
            break
        opts = []
        if len(S) < d - 1:
            for s in cB:
                g = (ux & B3[s]).bit_count() + (uy & B2[s]).bit_count()
                opts.append((g, 0, s))
        if len(T) < d - 1:
            for t in cA:
                g = (ux & B2[t]).bit_count() + (uy & B3[t]).bit_count()
                opts.append((g, 1, t))
        if not opts:
            break
        best = max(o[0] for o in opts)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            pick = rng.choice([o for o in opts if o[0] >= thresh])
        else:
            pick = rng.choice([o for o in opts if o[0] == best])
        _, kind, v = pick
        if kind == 0:
            S.append(v)
            ux &= ~B3[v]
            uy &= ~B2[v]
            cB.remove(v)
        else:
            T.append(v)
            ux &= ~B2[v]
            uy &= ~B3[v]
            cA.remove(v)
    if ux or uy:
        return None
    return S, T


# ----------------------------------------------------------------------------
# Diameter-safe shortcut edges between spare opposite-side vertices.
# ----------------------------------------------------------------------------

def _shortcut(edges, adj, color, spare, d, reach, rng):
    """Add one edge between a random spare vertex and the spare opposite-side vertex that gains most coverage."""
    s = rng.choice(spare)
    nb = set(adj[s])
    best, bg = None, -1
    for v in spare:
        if v == s or color[v] == color[s] or v in nb or len(adj[v]) >= d:
            continue
        g = (reach[v] & ~reach[s]).bit_count()
        if g > bg:
            bg, best = g, v
    if best is None:
        return False
    edges.append((s, best))
    adj[s].append(best)
    adj[best].append(s)
    return True


def _extend(n, edges, d, deadline, rng, max_fails):
    """Greedily add vertices (single or joint pairs) keeping max degree d and diameter 4; return (n, edges)."""
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
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        B2, B3 = _balls23(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        c0 = color[s0]
        pool_all = [v for v in spare if color[v] == c0]
        pool_opp = [v for v in spare if color[v] != c0]

        # Single-vertex move first.
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, B3, full, d, rng, noise)
            if S is not None:
                break
        if S is not None:
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - c0)
            fails = 0
            continue

        # Joint pair move: x (colour c0) with y (colour 1-c0), joined by an edge.
        res = None
        if pool_all and pool_opp:
            for attempt in range(3):
                noise = 0.0 if attempt == 0 else rng.choice([0.15, 0.3])
                res = _pair_attempt(pool_all, pool_opp, B2, B3, full, d, rng, noise)
                if res is not None:
                    break
        if res is not None:
            S_, T_ = res
            x = n
            y = n + 1
            n += 2
            edges.append((x, y))
            adj.append([y] + list(S_))
            adj.append([x] + list(T_))
            for s in S_:
                edges.append((s, x))
                adj[s].append(x)
            for t in T_:
                edges.append((t, y))
                adj[t].append(y)
            color.append(c0)
            color.append(1 - c0)
            fails = 0
            continue

        fails += 1
        if fails % 2 == 0:
            _shortcut(edges, adj, color, spare, d, B3, rng)
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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
            return True
        return False

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

    # Twin graph on W(d-2), then randomized single and joint-pair extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
