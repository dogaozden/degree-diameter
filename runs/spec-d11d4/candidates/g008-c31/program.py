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

def _twin_graph(q, dl_I, dl_J, rng):
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

    I = _mis(P, [sorted(s) for s in padj], dl_I, rng)
    J = _mis(L, [sorted(s) for s in ladj], dl_J, rng)

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
# NEW routine: cover-augmentation.
#
# A new vertex x on side c can be joined to up to d vertices of the opposite
# side that still have a spare degree slot. Adding x keeps every old pair
# within distance D exactly when the union of the radius-(D-1) balls of its
# neighbours covers the whole current graph (x reaches w through a neighbour s
# iff dist(s, w) <= D-1). Because the check uses the current graph, vertices
# added earlier are counted too, so new-new pairs are verified automatically.
# We greedily pick neighbours by how many new vertices their 3-balls cover,
# with randomized tie-breaking and restarts, and add x whenever full cover is
# reached. Balls are kept as Python big-int bitsets.
# ----------------------------------------------------------------------------

def _bitballs(n, adj, r):
    """Bit v of result[u] is set iff dist(u, v) <= r in the current graph."""
    R = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = R[v]
            for u in adj[v]:
                x |= R[u]
            new.append(x)
        R = new
    return R


def _side_colors(n, adj):
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if side[w] == -1:
                    side[w] = 1 - side[u]
                    stack.append(w)
    return side


def _augment(n, edges, d, D, deadline, rng):
    """Greedily add vertices joined to spare-slot vertices whose (D-1)-balls cover the graph."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = _side_colors(n, adj)
    out = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        R = _bitballs(n, adj, D - 1)
        full = (1 << n) - 1
        ok = False
        for attempt in range(40):
            if time.monotonic() >= deadline:
                break
            c = attempt % 2
            cands = [v for v in range(n) if side[v] == 1 - c and len(adj[v]) < d]
            if not cands:
                continue
            rng.shuffle(cands)
            noise = 0.0 if attempt < 2 else 1.5
            covered = 0
            chosen = []
            for _ in range(d):
                best_v, best_s, best_g = None, -1.0, 0
                for v in cands:
                    if v in chosen:
                        continue
                    g = (R[v] & ~covered).bit_count()
                    if g == 0:
                        continue
                    s = g + noise * rng.random()
                    if s > best_s:
                        best_v, best_s, best_g = v, s, g
                if best_v is None:
                    break
                chosen.append(best_v)
                covered |= R[best_v]
                if covered == full:
                    break
            if covered == full and chosen:
                x = n
                n += 1
                for v in chosen:
                    adj[v].append(x)
                    out.append((v, x))
                adj.append(list(chosen))
                side.append(c)
                ok = True
                break
        fails = 0 if ok else fails + 1
    return n, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 14.0))
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

    # Twin graph on W(d-2) plus cover-augmentation on its spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            dl_I = t0 + 0.45 * budget
            dl_J = t0 + 0.70 * budget
            n, edges = _twin_graph(d - 2, dl_I, dl_J, rng)
            consider(n, edges)
            n2, e2 = _augment(n, edges, d, D, deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
