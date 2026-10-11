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


def _gq_incidence(P, lines):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps
# (ARW-style). Used to find a large partial ovoid of W(q) (points pairwise
# non-collinear) and a large partial spread (lines pairwise disjoint).
# ----------------------------------------------------------------------------

def _ils_mis(n, adj, deadline, rng, target=None):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    nbr = [set(a) for a in adj]
    inS = [False] * n
    tight = [0] * n          # number of neighbours of v inside the solution
    Sset = set()

    def ins(v):
        inS[v] = True
        Sset.add(v)
        for w in adj[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        Sset.discard(v)
        for w in adj[v]:
            tight[w] -= 1

    def fill():
        free = [v for v in range(n) if not inS[v] and tight[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def improve():
        moved = True
        while moved:
            moved = False
            order = list(Sset)
            rng.shuffle(order)
            for x in order:
                if not inS[x]:
                    continue
                C = [u for u in adj[x] if not inS[u] and tight[u] == 1]
                if len(C) < 2:
                    continue
                rng.shuffle(C)
                pair = None
                for i in range(len(C)):
                    a = C[i]
                    for j in range(i + 1, len(C)):
                        if C[j] not in nbr[a]:
                            pair = (a, C[j])
                            break
                    if pair:
                        break
                if pair:
                    rem(x)
                    ins(pair[0])
                    ins(pair[1])
                    fill()
                    moved = True

    fill()
    improve()
    best = list(Sset)
    if target is not None and len(best) >= target:
        return best
    while time.monotonic() < deadline:
        v = rng.randrange(n)
        if inS[v]:
            continue
        for w in list(adj[v]):
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        improve()
        if len(Sset) > len(best):
            best = list(Sset)
            if target is not None and len(best) >= target:
                break
        elif len(Sset) < len(best) - 2:
            # Drift too far from the best solution: restart from it.
            for v2 in list(Sset):
                rem(v2)
            for v2 in best:
                ins(v2)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Point-side new vertices attach to the 10-ish lines through each point of an
# independent set I of points (pairwise non-collinear: a partial ovoid).
# Line-side new vertices attach to the points of each line of an independent
# set J of lines (pairwise disjoint: a partial spread). The two constraints are
# independent, so I and J are searched separately, each as a maximum
# independent set.
# ----------------------------------------------------------------------------

def _twin_edges(P, lines, pl, I, J, L):
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
# Greedy set-cover vertex extension for diameter 4.
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# existing vertex. Adding x only shortens distances, so no other pair can break.
# ----------------------------------------------------------------------------

NOISE = 0.25


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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
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
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


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
            P1, lines1 = _gq_w(d - 1)
            consider(*_gq_incidence(P1, lines1))
        except Exception:
            pass

    # Twin graph on W(q), q = d-2, with partial ovoid I and partial spread J
    # each found by iterated local search, then randomized set-cover extension.
    q = d - 2
    if D >= 4 and lib.is_prime_power(q) and 2 <= q <= 9:
        try:
            P, lines = _gq_w(q)
            L = len(lines)
            pl = [[] for _ in range(P)]
            for j, Ls in enumerate(lines):
                for p in Ls:
                    pl[p].append(j)
            padj = [set() for _ in range(P)]     # collinear points
            for Ls in lines:
                for p in Ls:
                    for r in Ls:
                        if p != r:
                            padj[p].add(r)
            ladj = [set() for _ in range(L)]     # lines sharing a point
            for p in range(P):
                for a in pl[p]:
                    for b in pl[p]:
                        if a != b:
                            ladj[a].add(b)

            now = time.monotonic()
            span = max(0.0, deadline - now)
            # Spread target: P/(q+1) lines pairwise disjoint covering all points.
            J = _ils_mis(L, [sorted(s) for s in ladj], now + 0.25 * span, rng,
                         target=P // (q + 1))
            # Partial ovoid: Tallini bound q^2-q+1 for odd q (a loose upper target).
            I = _ils_mis(P, [sorted(s) for s in padj], now + 0.85 * span, rng,
                         target=q * q - q + 1)

            n2, e2 = _twin_edges(P, lines, pl, I, J, L)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
