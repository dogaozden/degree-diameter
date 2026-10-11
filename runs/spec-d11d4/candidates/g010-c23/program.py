import itertools
import random
import sys
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
# NEW: exact-cover style search for a spread of W(q).
#
# A spread is a set of pairwise disjoint lines covering every point. If the
# spread has size P/(q+1) = q^2+1, then the line-side twins (one per spread
# line, each using the spare slot of its line's points) use every point's
# spare slot exactly once. Randomised DFS: always branch on the uncovered point
# with fewest still-available lines, with node limits and restarts.
# ----------------------------------------------------------------------------

def _spread(P, lines, pl, target, deadline, rng, node_limit=1500):
    """Return a list of pairwise disjoint line indices (ideally of size target), found before deadline."""
    L = len(lines)
    best = []
    while time.monotonic() < deadline:
        covered = [False] * P
        ok = [True] * L
        chosen = []
        nodes = [0]

        def dfs():
            if len(chosen) > len(best):
                best[:] = chosen
            if len(chosen) >= target:
                return True
            nodes[0] += 1
            if nodes[0] > node_limit or time.monotonic() > deadline:
                return False
            pick = None
            for p in range(P):
                if covered[p]:
                    continue
                opts = [M for M in pl[p] if ok[M]]
                if not opts:
                    return False
                if pick is None or len(opts) < len(pick[1]):
                    pick = (p, opts)
                    if len(opts) == 1:
                        break
            if pick is None:
                return False
            opts = pick[1]
            rng.shuffle(opts)
            for M in opts:
                pts = lines[M]
                for x in pts:
                    covered[x] = True
                killed = []
                for x in pts:
                    for N in pl[x]:
                        if ok[N]:
                            ok[N] = False
                            killed.append(N)
                chosen.append(M)
                if dfs():
                    return True
                chosen.pop()
                for N in killed:
                    ok[N] = True
                for x in pts:
                    covered[x] = False
                if nodes[0] > node_limit or time.monotonic() > deadline:
                    return False
            return False

        if dfs():
            return list(chosen)
    return list(best)


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Parity-respecting distances are all <= 4 (checked in the analysis), and
# lib.is_valid guards the final output.
# ----------------------------------------------------------------------------

def _twin_graph(P, lines, deadline, rng):
    L = len(lines)
    k = len(lines[0])
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

    padj_l = [sorted(s) for s in padj]
    ladj_l = [sorted(s) for s in ladj]

    now = time.monotonic()
    total = max(0.5, deadline - now)
    # Point twins: partial ovoid (pairwise non-collinear points).
    I = _mis(P, padj_l, now + 0.5 * total, rng)
    # Line twins: partial spread via exact-cover DFS, then MIS as a backup.
    t2 = time.monotonic()
    J1 = _spread(P, lines, pl, P // k, t2 + 0.3 * total, rng)
    J2 = _mis(L, ladj_l, deadline, rng)
    J = J1 if len(J1) >= len(J2) else J2

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
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
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

    gq_cache = {}

    def gq(q):
        if q not in gq_cache:
            gq_cache[q] = _gq_w(q)
        return gq_cache[q]

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            P, lines = gq(d - 1)
            consider(*_gq_incidence(P, lines))
        except Exception:
            pass

    # W(d-2) with twins using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            P, lines = gq(d - 2)
            consider(*_twin_graph(P, lines, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
