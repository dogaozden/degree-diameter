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
# NEW: exact spread search. A spread of W(q) is a set of pairwise disjoint lines
# covering every point. Found by DFS with a minimum-remaining-values rule and a
# blocked-line counter, so each node costs O(P * q).
# ----------------------------------------------------------------------------

def _exact_spread(P, lines, deadline, rng, node_limit=10 ** 6):
    """Return a list of line indices forming a spread (disjoint, covering all points), or None."""
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    if any(not x for x in pl):
        return None
    for x in pl:
        rng.shuffle(x)
    covered = [False] * P
    blocked = [0] * L
    chosen = []
    nodes = [0]

    def take(j, delta):
        for r in lines[j]:
            covered[r] = delta > 0
            for k in pl[r]:
                blocked[k] += delta

    def dfs(remaining):
        if remaining == 0:
            return True
        nodes[0] += 1
        if nodes[0] > node_limit or time.monotonic() > deadline:
            return False
        best_opts = None
        for p in range(P):
            if covered[p]:
                continue
            opts = [j for j in pl[p] if blocked[j] == 0]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
                if len(opts) == 1:
                    break
        rng.shuffle(best_opts)
        for j in best_opts:
            take(j, 1)
            chosen.append(j)
            if dfs(remaining - len(lines[j])):
                return True
            chosen.pop()
            take(j, -1)
        return False

    if dfs(P):
        return list(chosen)
    return None


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p;
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines, preferably a
#     full spread so every point gets one), adjacent to all points of L.
# Returns (n, edges, side) where side[v] is 0 for point-side, 1 for line-side.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
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

    now = time.monotonic()
    total = max(0.0, deadline - now)
    J = _exact_spread(P, lines, now + 0.3 * total, rng)
    if J is None:
        J = _mis(L, [sorted(s) for s in ladj], now + 0.45 * total, rng)
    I = _mis(P, [sorted(s) for s in padj], now + 0.75 * total, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    side = [0] * P + [1] * L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        side.append(0)
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        side.append(1)
        n += 1
    return n, edges, side


# ----------------------------------------------------------------------------
# NEW: spare-slot augmentation with exact reachability.
#
# Adding a vertex x never increases distances between old vertices, so the graph
# stays within diameter D iff x reaches every vertex within D. If x is joined to a
# set S of opposite-side vertices with spare degree, then dist(x, w) <= D iff some
# s in S has dist(s, w) <= D-1. The radius-(D-1) balls are stored as bitmasks, so
# choosing S is a greedy set cover, and each candidate is checked exactly.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            m = reach[v]
            for u in adj[v]:
                m |= reach[u]
            new.append(m)
        reach = new
    return reach


def _spare_augment(n, edges, side, d, D, deadline, rng):
    """Greedily add vertices on spare degree while keeping diameter <= D. Returns (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = list(side)
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 25:
        n_cur = len(adj)
        full = (1 << n_cur) - 1
        masks = _ball_masks(n_cur, adj, D - 1)
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for s_new in sides:
            opp = 1 - s_new
            cand = [v for v in range(n_cur) if side[v] == opp and len(adj[v]) < d]
            if not cand:
                continue
            rng.shuffle(cand)
            cov = 0
            S = []
            while cov != full and len(S) < d and cand:
                bestv, bestg, bi = -1, -1, -1
                for i, v in enumerate(cand):
                    g = (masks[v] & ~cov).bit_count()
                    if g > bestg:
                        bestg, bestv, bi = g, v, i
                if bestg <= 0:
                    break
                S.append(bestv)
                cov |= masks[bestv]
                cand.pop(bi)
            if cov == full:
                x = n_cur
                adj.append([])
                side.append(s_new)
                for v in S:
                    adj[v].append(x)
                    adj[x].append(v)
                    edges.append((v, x))
                placed = True
                break
        fails = 0 if placed else fails + 1
    return len(adj), edges


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

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twins on W(d-2) (degree d, diameter 4), then spare-slot augmentation.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n, edges, side = _twin_graph(d - 2, t0 + 0.7 * budget, rng)
            if lib.is_valid(n, edges, d, D):
                consider(n, edges)
                n2, e2 = _spare_augment(n, edges, side, d, D, deadline, rng)
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
