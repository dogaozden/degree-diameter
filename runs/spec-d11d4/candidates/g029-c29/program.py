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
# NEW: tracked set-cover extension for diameter 4.
#
# Maintains exact-or-underestimated ball masks b2 (radius 2) and b3 (radius 3)
# as Python int bitsets, updated incrementally when a vertex is added. A new
# vertex x with neighbour set S (all of one colour class) is accepted only if
# the union of b3[s] over S covers every current vertex. Since adding a vertex
# never increases a distance, pairs already within 4 stay within 4, and the
# only new pairs are those involving x, so validity is preserved at each step.
# Underestimating b2/b3 is safe: it can only reject candidates, never accept
# invalid ones. This fixes the stale-reach issue of a single snapshot.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _bits(m):
    """Yield the indices of set bits of a non-negative int."""
    while m:
        low = m & -m
        yield low.bit_length() - 1
        m ^= low


def _extend_tracked(n, edges, d, deadline, rng, max_fails=4000):
    """Greedily add degree-<=d vertices with tracked reach masks; return (n, edges), always diameter <= 4."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    adjm = [0] * n
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        adjm[u] |= 1 << v
        adjm[v] |= 1 << u

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

    b2 = [0] * n
    for v in range(n):
        m = (1 << v) | adjm[v]
        for u in adj[v]:
            m |= adjm[u]
        b2[v] = m
    b3 = [0] * n
    for v in range(n):
        m = 1 << v
        for u in adj[v]:
            m |= b2[u]
        b3[v] = m

    fails = 0
    while time.monotonic() < deadline:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare or fails >= max_fails:
            break
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool = [v for v in spare if color[v] == color[s0] and v != s0]
        S = [s0]
        unc = full & ~b3[s0]
        while unc and len(S) < d and pool:
            if rng.random() < NOISE:
                useful = [v for v in pool if b3[v] & unc]
                if not useful:
                    break
                bv = rng.choice(useful)
            else:
                best_g, bv = 0, -1
                for v in pool:
                    g = (b3[v] & unc).bit_count()
                    if g > best_g:
                        best_g, bv = g, v
                if bv < 0:
                    break
            S.append(bv)
            unc &= ~b3[bv]
            pool.remove(bv)
        if unc:
            fails += 1
            continue

        # Accept: new vertex x adjacent to S.
        x = n
        n += 1
        Sm = 0
        N2S = 0
        B2S = 0
        for s in S:
            Sm |= 1 << s
            N2S |= adjm[s]
            B2S |= b2[s]
        for s in S:
            adjm[s] |= 1 << x
            adj[s].append(x)
            edges.append((s, x))
        adj.append(list(S))
        adjm.append(Sm)
        color.append(1 - color[s0])
        # Radius-2 masks: old vertices within 1 of S, and S members, gain x.
        for v in _bits(Sm | N2S):
            b2[v] |= 1 << x
        for s in S:
            b2[s] |= Sm
        # Radius-3 masks: old vertices within 2 of S gain x.
        for v in _bits(B2S):
            b3[v] |= 1 << x
        b2.append((1 << x) | Sm | N2S)
        b3.append((1 << x) | B2S)
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + 0.9 * budget
    twin_deadline = t0 + 0.3 * budget
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

    # Twin graph on W(d-2), then tracked set-cover extension with restarts.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            while time.monotonic() < deadline - 0.5:
                now = time.monotonic()
                remaining = deadline - now
                slice_end = min(deadline, now + max(2.0, remaining / 3.0))
                n3, e3 = _extend_tracked(n2, e2, d, slice_end, rng)
                consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
