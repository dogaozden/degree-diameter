import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

_GQ_CACHE = {}


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


def _gq_w_cached(q):
    if q not in _GQ_CACHE:
        _GQ_CACHE[q] = _gq_w(q)
    return _GQ_CACHE[q]


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w_cached(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with (1,2)-swaps.
#
# Arw-style ILS: a solution S is kept with a tightness count per vertex
# (number of solution neighbours). A (1,2)-swap removes one solution vertex x
# and inserts two non-adjacent vertices whose only solution neighbour is x.
# Perturbation forces a random outside vertex in, then local search repairs.
# ----------------------------------------------------------------------------

def _ils(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    adjs = [set(a) for a in adj]
    inS = [False] * n
    tight = [0] * n
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            tight[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in adj[v]:
            tight[w] -= 1

    def fill(cands):
        cands = list(cands)
        rng.shuffle(cands)
        for v in cands:
            if not inS[v] and tight[v] == 0:
                ins(v)

    def two_improve(stack):
        while stack:
            x = stack.pop()
            if not inS[x]:
                continue
            L = [v for v in adj[x] if not inS[v] and tight[v] == 1]
            if len(L) < 2:
                continue
            rng.shuffle(L)
            pair = None
            for i in range(len(L)):
                au = adjs[L[i]]
                for j in range(i + 1, len(L)):
                    if L[j] not in au:
                        pair = (L[i], L[j])
                        break
                if pair is not None:
                    break
            if pair is None:
                continue
            rem(x)
            ins(pair[0])
            ins(pair[1])
            fill(adj[x])
            for v in adj[x]:
                for y in adj[v]:
                    if inS[y]:
                        stack.append(y)

    order = list(range(n))
    rng.shuffle(order)
    fill(order)
    two_improve(list(S))
    best = list(S)
    saved = list(S)
    while time.monotonic() < deadline:
        v = rng.randrange(n)
        if inS[v]:
            continue
        nb = [w for w in adj[v] if inS[w]]
        for w in nb:
            rem(w)
        ins(v)
        near = []
        for w in nb:
            near.extend(adj[w])
        fill(near)
        stack = [v]
        for w in adj[v]:
            for y in adj[w]:
                if inS[y]:
                    stack.append(y)
        two_improve(stack)
        if len(S) > len(best):
            best = list(S)
        if len(S) >= len(saved) or rng.random() < 0.02:
            saved = list(S)
        else:
            for u in list(S):
                rem(u)
            for u in saved:
                ins(u)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Non-collinear points are at distance 4 and disjoint lines are at distance 4,
# which keeps every pair within distance 4. The final lib.is_valid check
# guards against any mistake.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w_cached(q)
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
    I = _ils(P, [sorted(s) for s in padj], mid, rng)
    J = _ils(L, [sorted(s) for s in ladj], deadline, rng)

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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 15.0))
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

    # Twins on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
