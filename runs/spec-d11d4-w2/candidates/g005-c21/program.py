import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (pure Python).
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
# NEW CONSTRUCTION: spare-slot cover extension.
#
# Let G be a valid bipartite graph with max degree d and diameter <= D. Adding
# a new vertex x of colour c, joined to a set S of opposite-colour vertices that
# still have spare degree, keeps G valid exactly when every old vertex v lies
# within distance D-1 of some s in S (then dist(x, v) <= D). Adding edges can
# only shorten distances, so no previously checked pair can break.
#
# So the extension is a set-cover problem: cover all vertices with the radius
# (D-1) balls of at most d spare candidates, found by greedy max-coverage with
# randomized tie-breaks. Ball bitmasks are recomputed after every insertion
# so the coverage data is always exact. When no vertex fits, a random
# shortcut edge between spare vertices of opposite colour is added (it only
# shortens distances) and the attempt is repeated a bounded number of times.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """reach[v] = bitmask of all vertices within distance r of v."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt.append(x)
        reach = nxt
    return reach


def _attach(n, adj, color, d, D, rng):
    """Find (colour, S) for a new vertex that keeps diameter <= D, or None."""
    R = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    for c in (0, 1):
        pool = [v for v in range(n) if color[v] == 1 - c and len(adj[v]) < d]
        if not pool:
            continue
        rng.shuffle(pool)
        unc = full
        S = []
        while unc and len(S) < d and pool:
            bi, bg = -1, 0
            for i, v in enumerate(pool):
                g = (R[v] & unc).bit_count()
                if g > bg:
                    bg, bi = g, i
            if bi < 0:
                break
            v = pool.pop(bi)
            S.append(v)
            unc &= ~R[v]
        if unc == 0 and S:
            return c, S
    return None


def _shortcut(n, adj, color, d, rng):
    """Random non-adjacent pair of spare vertices of opposite colour, or None."""
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not A or not B:
        return None
    for _ in range(100):
        u = rng.choice(A)
        v = rng.choice(B)
        if v not in adj[u]:
            return u, v
    return None


def _extend(n, edges, d, D, deadline, rng, max_shortcuts=60):
    """Grow a valid bipartite graph by spare-slot cover extension; returns (n, edges)."""
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
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return n, list(edges)  # not bipartite: leave unchanged
    edges = list(edges)
    shortcuts = 0
    while time.monotonic() < deadline:
        res = _attach(n, adj, color, d, D, rng)
        if res is not None:
            c, S = res
            x = n
            n += 1
            adj.append([])
            color.append(c)
            for s in S:
                adj[s].append(x)
                adj[x].append(s)
                edges.append((x, s))
            continue
        if shortcuts >= max_shortcuts:
            break
        sc = _shortcut(n, adj, color, d, rng)
        if sc is None:
            break
        u, v = sc
        adj[u].append(v)
        adj[v].append(u)
        edges.append((u, v))
        shortcuts += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    end = t0 + budget
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
            consider(*_gq_incidence_from(d - 1))
        except Exception:
            pass

    # W(d-2) has degree d-1, leaving one spare slot per vertex.
    # Extend it with the cover construction, then add the twin construction
    # and extend that too.
    if D >= 4 and d >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            P, lines = _gq_w(d - 2)
            L = len(lines)
            inc_n = P + L
            inc_e = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(inc_n, inc_e)
            consider(*_extend(inc_n, inc_e, d, D, t0 + 0.2 * budget, rng))

            attempts = 0
            while attempts < 2 and time.monotonic() < end - 2.0:
                now = time.monotonic()
                remain = end - now
                tn, te = _twin_graph(P, lines, now + 0.5 * remain, rng)
                consider(tn, te)
                consider(*_extend(tn, te, d, D, end, rng))
                attempts += 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best


def _gq_incidence_from(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
