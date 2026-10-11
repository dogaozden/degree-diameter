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
# Independent-set search: iterated local search with (1,2)-swaps
# (Andrade-Resende-Werneck style). Pure Python.
# ----------------------------------------------------------------------------

def _ils(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    adjset = [set(a) for a in adj]
    inS = [False] * n
    tau = [0] * n        # number of solution neighbours of each vertex
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            tau[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in adj[v]:
            tau[w] -= 1

    def fill():
        free = [v for v in range(n) if not inS[v] and tau[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and tau[v] == 0:
                ins(v)

    def improve():
        """Apply (1,2)-swaps until none exists: remove x, insert two non-adjacent 1-tight neighbours of x."""
        changed = True
        while changed:
            changed = False
            xs = list(S)
            rng.shuffle(xs)
            for x in xs:
                if not inS[x]:
                    continue
                L = [u for u in adj[x] if tau[u] == 1]
                if len(L) < 2:
                    continue
                found = None
                for i in range(len(L)):
                    for j in range(i + 1, len(L)):
                        if L[j] not in adjset[L[i]]:
                            found = (L[i], L[j])
                            break
                    if found:
                        break
                if found:
                    rem(x)
                    ins(found[0])
                    ins(found[1])
                    fill()
                    changed = True

    fill()
    improve()
    best = list(S)
    while time.monotonic() < deadline:
        cur = list(S)
        # Perturbation: force one non-solution vertex in, dropping its solution neighbours.
        v = rng.randrange(n)
        tries = 0
        while inS[v] and tries < 50:
            v = rng.randrange(n)
            tries += 1
        if inS[v]:
            continue
        for w in list(adj[v]):
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        improve()
        if len(S) > len(best):
            best = list(S)
        if len(S) < len(cur) and rng.random() < 0.8:
            # Revert to the previous local optimum most of the time.
            for x in list(S):
                rem(x)
            for x in cur:
                ins(x)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Distances: every new vertex is within distance 4 of everything (checked
# below by lib.is_valid as a final guard). I and J are chosen independently
# by iterated local search, which is much stronger than the greedy tabu used before.
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

    # Twin graph on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
