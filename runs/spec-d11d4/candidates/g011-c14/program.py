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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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
# Augmentation: attach new vertices to spare degree slots.
#
# A new vertex x on the side opposite to a colour class Y, adjacent to a set S
# of spare vertices of Y, keeps the graph within diameter D exactly when every
# vertex v of the graph lies within distance D-1 of some s in S. Adding x only
# shortens distances, so existing pairs stay valid. We find S greedily with
# bitmask balls, then check the whole graph periodically with lib.is_valid,
# reverting to the last validated state on any failure.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, deadline, rng):
    if D < 2 or d < 1 or n < 2:
        return n, edges
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    color[0] = 0
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if color[v] == -1:
                color[v] = 1 - color[u]
                stack.append(v)
    if -1 in color:
        return n, edges

    edges = list(edges)
    good_n, good_m = n, len(edges)
    added = 0
    while time.monotonic() < deadline:
        # Balls of radius D-1 as bitmasks.
        R = [1 << v for v in range(n)]
        for _ in range(D - 1):
            newR = []
            for v in range(n):
                r = R[v]
                for u in adj[v]:
                    r |= R[u]
                newR.append(r)
            R = newR
        full = (1 << n) - 1

        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for Y in sides:
            spare = [v for v in range(n) if color[v] == Y and len(adj[v]) < d]
            rng.shuffle(spare)
            chosen = []
            unc = full
            while unc and len(chosen) < d and spare:
                bi, bg = -1, 0
                for i, v in enumerate(spare):
                    g = (R[v] & unc).bit_count()
                    if g > bg:
                        bg, bi = g, i
                if bi < 0:
                    break
                v = spare.pop(bi)
                chosen.append(v)
                unc &= ~R[v]
            if unc == 0 and chosen:
                x = n
                n += 1
                color.append(1 - Y)
                adj.append([])
                for s in chosen:
                    adj[s].append(x)
                    adj[x].append(s)
                    edges.append((s, x))
                placed = True
                break
        if not placed:
            break
        added += 1
        if added % 40 == 0:
            if not lib.is_valid(n, edges, d, D):
                return good_n, edges[:good_m]
            good_n, good_m = n, len(edges)

    if lib.is_valid(n, edges, d, D):
        return n, edges
    return good_n, edges[:good_m]


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + total
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

    # Twin graph on W(d-2) (degree d, diameter 4), then greedy augmentation
    # into the remaining spare slots. The plain twin graph stays as a fallback.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            tw = _twin_graph(d - 2, t0 + 0.55 * total, rng)
            consider(*tw)
            try:
                aug = _augment(tw[0], tw[1], d, D, deadline - 2.0, rng)
                consider(*aug)
            except Exception:
                pass
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
