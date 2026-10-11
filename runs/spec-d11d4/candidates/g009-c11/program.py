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
# W(q) built over GF(q^2) with the trace form Tr(x1*y2 - x2*y1). Its lines
# include the Desarguesian spread {lambda*v : lambda in GF(q^2)*}, which
# gives q^2+1 pairwise disjoint lines covering all points.
# ----------------------------------------------------------------------------

def _gq_spread(q):
    """Return (P, lines, spread): W(q) points, all lines, and spread (line indices), or spread None."""
    N = q * q
    F = lib.GF(N)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(N) if add[a][b] == 0) for a in range(N)]
    pw = [F.pow(t, q) for t in range(N)]
    tr = [add[t][pw[t]] for t in range(N)]          # trace GF(q^2) -> GF(q)
    K = [x for x in range(N) if pw[x] == x]         # subfield GF(q)
    if len(K) != q:
        raise ValueError("subfield size mismatch")
    S = [s for s in K if s]

    def canon(a, b):
        return min((mul[s][a], mul[s][b]) for s in S)

    reps = []
    pid = {}
    for a in range(N):
        for b in range(N):
            if a or b:
                c = canon(a, b)
                if c not in pid:
                    pid[c] = len(reps)
                    reps.append(c)
    P = len(reps)

    def orth(i, j):
        x1, x2 = reps[i]
        y1, y2 = reps[j]
        return tr[add[mul[x1][y2]][neg[mul[x2][y1]]]] == 0

    lines = []
    covered = set()
    for i in range(P):
        for j in range(i + 1, P):
            if (i * P + j) in covered or not orth(i, j):
                continue
            p1, p2 = reps[i]
            r1, r2 = reps[j]
            Ls = set()
            for a in K:
                for b in K:
                    if a or b:
                        Ls.add(pid[canon(add[mul[a][p1]][mul[b][r1]],
                                         add[mul[a][p2]][mul[b][r2]])])
            Ls = sorted(Ls)
            if len(Ls) != q + 1:
                raise ValueError("line size mismatch")
            lines.append(Ls)
            for x in Ls:
                for y in Ls:
                    if x < y:
                        covered.add(x * P + y)

    lineidx = {tuple(L): k for k, L in enumerate(lines)}
    vs = [(1, t) for t in range(N)] + [(0, 1)]
    sp = []
    for v1, v2 in vs:
        Ls = tuple(sorted({pid[canon(mul[l][v1], mul[l][v2])] for l in range(1, N)}))
        k = lineidx.get(Ls)
        if k is None:
            return P, lines, None
        sp.append(k)
    cov = set()
    for k in sp:
        cov.update(lines[k])
    if len(cov) == P and len(sp) * (q + 1) == P:
        return P, lines, sp
    return P, lines, None


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
# Twin constructions on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Spread J covers every point exactly once, so J has q^2+1 lines (the maximum).
# I is found by tabu search for a partial ovoid.
# ----------------------------------------------------------------------------

def _twin_spread(q, deadline, rng):
    """Twin graph on W(q) with J = a spread of W(q) and I found by search; (n, edges) or None."""
    res = _gq_spread(q)
    P, lines, spread = res
    if spread is None:
        return None
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

    I = _mis(P, [sorted(s) for s in padj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for k in spread:
        for p in lines[k]:
            edges.append((p, n))
        n += 1
    return n, edges


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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Twin graph on W(d-2) (degree d, diameter 4). Preferred: spread-based J.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        ok = False
        try:
            res = _twin_spread(q, deadline, rng)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
                ok = True
        except Exception:
            pass
        if not ok:
            try:
                consider(*_twin_graph(q, deadline, rng))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
