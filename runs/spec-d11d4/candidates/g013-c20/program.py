import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (pts, lines, F): points of W(q) as normalized 4-vectors, each totally isotropic line as a sorted point-index list, and the field."""
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
    return pts, lines, F


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    pts, lines, _ = _gq_w(q)
    P = len(pts)
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
# Explicit spread of W(q): q^2+1 pairwise disjoint totally isotropic lines
# covering every point exactly once.
#
# Coordinates v = (x1, y1, x2, y2) with form x1*y1' - y1*x1' + x2*y2' - y2*x2'.
# For a symmetric 2x2 matrix M, the line {(x, Mx)} is totally isotropic.
# Take the plane {sI + tB} of symmetric matrices, chosen so every nonzero
# member is invertible. Its q^2 members give pairwise disjoint lines, and the
# extra line {x = 0} completes the spread.
# ----------------------------------------------------------------------------

def _spread(q, index, lines, F):
    """Return a list of q^2+1 line indices forming a spread of W(q), or None if the construction fails."""
    lines_index = {tuple(Ls): j for j, Ls in enumerate(lines)}

    def norm(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    def mat_at(s, t, B):
        return (F.add(s, F.mul(t, B[0])), F.mul(t, B[1]),
                F.mul(t, B[2]), F.add(s, F.mul(t, B[3])))

    def det(M):
        return F.sub(F.mul(M[0], M[3]), F.mul(M[1], M[2]))

    # Find symmetric B so that det(sI + tB) != 0 for all (s, t) != (0, 0).
    B = None
    for b00, b01, b11 in itertools.product(range(q), repeat=3):
        cand = (b00, b01, b01, b11)
        if all(det(mat_at(s, t, cand)) != 0
               for s in range(q) for t in range(q) if (s, t) != (0, 0)):
            B = cand
            break
    if B is None:
        return None

    mats = [mat_at(s, t, B) for s in range(q) for t in range(q)]
    if len(set(mats)) != q * q:
        return None

    point_sets = []
    for M in mats:
        ids = set()
        for x1, x2 in itertools.product(range(q), repeat=2):
            if not (x1 or x2):
                continue
            y1 = F.add(F.mul(M[0], x1), F.mul(M[1], x2))
            y2 = F.add(F.mul(M[2], x1), F.mul(M[3], x2))
            ids.add(index[norm((x1, y1, x2, y2))])
        point_sets.append(ids)
    # The "infinity" line {x = 0}.
    ids = set()
    for y1, y2 in itertools.product(range(q), repeat=2):
        if not (y1 or y2):
            continue
        ids.add(index[norm((0, y1, 0, y2))])
    point_sets.append(ids)

    result = []
    for ids in point_sets:
        key = tuple(sorted(ids))
        if len(key) != q + 1 or key not in lines_index:
            return None
        result.append(lines_index[key])
    if len(set(result)) != len(result):
        return None
    return result


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# The two choices are independent. J is a full spread when available, so every
# point gets exactly one line twin. I is searched by tabu MIS on the
# collinearity graph. Non-collinear points and disjoint lines are at distance 4,
# and the final lib.is_valid check guards against any mistake.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    pts, lines, F = _gq_w(q)
    P = len(pts)
    L = len(lines)
    index = {v: i for i, v in enumerate(pts)}
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

    J = _spread(q, index, lines, F)
    if J is None:
        now = time.monotonic()
        mid = now + (deadline - now) / 2.0
        J = _mis(L, [sorted(s) for s in ladj], mid, rng)
    I = _mis(P, [sorted(s) for s in padj], deadline, rng)

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

    # Twin graph on W(d-2) (degree d, diameter 4), with the line side a spread.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
