import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) built from the field F_{q^2}.
#
# Points are the projective points of F_q^4, identified with K^2 for K = F_{q^2}.
# The alternating form is B(x, y) = Tr_{K/F}(det(x, y)), where det is the
# K-determinant. Its K-lines {z*v : z in K} are totally isotropic, so they
# form a spread of W(q): q^2+1 pairwise disjoint lines covering every point.
# This explicit spread is the new helper. It gives the maximum number of
# line-side twins (one per spread line), so no search is needed for that side.
# ----------------------------------------------------------------------------

def _gq(q):
    """Return (P, lines, spread) for W(q). lines: all totally isotropic lines as sorted point lists.
    spread: q^2+1 pairwise disjoint lines covering all points, or None if the check fails."""
    K = lib.GF(q * q)
    Q = q * q
    kadd = K.add_table.tolist()
    kmul = K.mul_table.tolist()
    kneg = [K.neg(a) for a in range(Q)]
    kinv = [0] + [K.inv(a) for a in range(1, Q)]
    F = [z for z in range(Q) if K.pow(z, q) == z]          # subfield F_q
    theta = next(z for z in range(Q) if K.pow(z, q) != z)  # K = F + F*theta
    coord = {}
    for a in F:
        for b in F:
            coord[kadd[a][kmul[b][theta]]] = (a, b)
    trt = [kadd[z][K.pow(z, q)] for z in range(Q)]          # trace K -> F

    def norm(v):
        c = next(x for x in v if x)
        ic = kinv[c]
        return tuple(kmul[ic][x] for x in v)

    pts = [v for v in itertools.product(F, repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)
    k2 = [(kadd[a1][kmul[b1][theta]], kadd[a2][kmul[b2][theta]]) for (a1, b1, a2, b2) in pts]

    def B(i, j):
        x1, x2 = k2[i]
        y1, y2 = k2[j]
        return trt[kadd[kmul[x1][y2]][kneg[kmul[x2][y1]]]]

    lines = []
    covered = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if i * P + j in covered or B(i, j):
                continue
            y = pts[j]
            Ls = set()
            for a in F:
                for b in F:
                    if a == 0 and b == 0:
                        continue
                    v = tuple(kadd[kmul[a][x[k]]][kmul[b][y[k]]] for k in range(4))
                    if any(v):
                        Ls.add(index[norm(v)])
            Ls = sorted(Ls)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)

    # Regular spread: one line per K-point of K^2.
    spread = []
    kvecs = [(1, t) for t in range(Q)] + [(0, 1)]
    for v1, v2 in kvecs:
        Ls = set()
        for z in range(1, Q):
            a1, b1 = coord[kmul[z][v1]]
            a2, b2 = coord[kmul[z][v2]]
            vec = (a1, b1, a2, b2)
            if any(vec):
                Ls.add(index[norm(vec)])
        spread.append(sorted(Ls))
    cover = set(p for s in spread for p in s)
    if sum(len(s) for s in spread) != P or len(cover) != P:
        spread = None
    return P, lines, spread


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
#   * point twin v_p for each p in I (I a partial ovoid: pairwise non-collinear),
#     adjacent to the q+1 lines through p. Each line gets at most one twin.
#   * line twin w_L for each L in J (J pairwise disjoint lines), adjacent to
#     the q+1 points of L. J = explicit spread when available (covers every point).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines, spread = _gq(q)
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
    padj = [sorted(s) for s in padj]

    now = time.monotonic()
    if spread is not None:
        Jsets = spread
        I = _mis(P, padj, deadline, rng)
    else:
        ladj = [set() for _ in range(L)]
        for p in range(P):
            for a in pl[p]:
                for b in pl[p]:
                    if a != b:
                        ladj[a].add(b)
        mid = now + (deadline - now) / 2.0
        I = _mis(P, padj, mid, rng)
        J = _mis(L, [sorted(s) for s in ladj], deadline, rng)
        Jsets = [lines[j] for j in J]

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for S in Jsets:
        for p in S:
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
            P, lines, _ = _gq(d - 1)
            edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(P + len(lines), edges)
        except Exception:
            pass

    # W(d-2) with twins using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
