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
# Bitmask balls and greedy cover helpers.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball_k(n, adj, k):
    """Return per-vertex bitmasks of all vertices within distance k."""
    reach = [1 << v for v in range(n)]
    for _ in range(k):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _ball3(n, adj):
    return _ball_k(n, adj, 3)


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


def _bicolor(n, adj):
    """Return a 2-colouring of every vertex (adj: neighbour sequences)."""
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
    return color


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# existing vertex. Adding x only shortens distances, so no other pair can break.
# ----------------------------------------------------------------------------

def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bicolor(n, adj)

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
# NEW: paired insertion ("pair-grow").
#
# Single-vertex cover extension needs one vertex x with d spare neighbours on
# the opposite side. A pair (x, y) with x on side X and y on side Y, joined by
# the edge x-y, has d-1 spare slots on each side. Its coverage is two-sided:
#
#   x reaches old v within 4 if v is in R3(S_x) or in R2(S_y)
#     (x - y - s' - ... - v uses the edge x-y and s' in S_y)
#   y reaches old v within 4 if v is in R3(S_y) or in R2(S_x)
#
# Both x and y must cover every old vertex. The two sets are grown jointly by
# greedy gain, which can succeed where a single vertex cannot: a vertex in S_y
# helps x through R2 as well as y through R3. Adding vertices never lengthens
# old distances, so only the two coverage conditions need checking. Every
# accepted pair is still verified with lib.is_valid and reverted on failure.
# ----------------------------------------------------------------------------

PNOISE = 0.2


def _pair_attempt(n, adj, color, reach3, reach2, d, rng):
    """Try to find sets (SX, SY) for a new pair; return (c, SX, SY) or None."""
    cap = d - 1
    full = (1 << n) - 1
    c = rng.randint(0, 1)
    poolY = [v for v in range(n) if color[v] == 1 - c and len(adj[v]) < d]
    poolX = [v for v in range(n) if color[v] == c and len(adj[v]) < d]
    if not poolX or not poolY:
        return None
    SX, SY = [], []
    uncX = full
    uncY = full
    while uncX or uncY:
        canY = len(SX) < cap and bool(poolY)
        canX = len(SY) < cap and bool(poolX)
        if not canX and not canY:
            return None
        gy = [((reach3[v] & uncX).bit_count() + (reach2[v] & uncY).bit_count(), v)
              for v in poolY] if canY else []
        gx = [((reach3[u] & uncY).bit_count() + (reach2[u] & uncX).bit_count(), u)
              for u in poolX] if canX else []
        by = max(gy) if gy else (-1, -1)
        bx = max(gx) if gx else (-1, -1)
        if rng.random() < PNOISE:
            cand = [("y", g, v) for g, v in gy if g > 0] + [("x", g, u) for g, u in gx if g > 0]
            if not cand:
                return None
            side, _, v = rng.choice(cand)
        else:
            if by[0] <= 0 and bx[0] <= 0:
                return None
            if by[0] >= bx[0]:
                side, v = "y", by[1]
            else:
                side, v = "x", bx[1]
        if side == "y":
            SX.append(v)
            poolY.remove(v)
            uncX &= ~reach3[v]
            uncY &= ~reach2[v]
        else:
            SY.append(v)
            poolX.remove(v)
            uncY &= ~reach3[v]
            uncX &= ~reach2[v]
    if not SX or not SY:
        return None
    return c, SX, SY


def _pair_grow(n, edges, d, D, deadline, rng):
    """Add valid vertex pairs until the deadline or repeated failure; return (n, edges), always valid."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, adj)
    reach3 = _ball_k(n, adj, 3)
    reach2 = _ball_k(n, adj, 2)

    fails = 0
    while time.monotonic() < deadline and fails < 400:
        res = _pair_attempt(n, adj, color, reach3, reach2, d, rng)
        if res is None:
            fails += 1
            continue
        c, SX, SY = res
        x, y = n, n + 1
        adj.append(set())
        adj.append(set())
        color.append(c)
        color.append(1 - c)
        added = [(x, y)]
        adj[x].add(y)
        adj[y].add(x)
        for s in SX:
            added.append((s, x))
            adj[s].add(x)
            adj[x].add(s)
        for u in SY:
            added.append((u, y))
            adj[u].add(y)
            adj[y].add(u)
        for a, b in added:
            eset.add((a, b) if a < b else (b, a))

        if lib.is_valid(n + 2, list(eset), d, D):
            n += 2
            reach3 = _ball_k(n, adj, 3)
            reach2 = _ball_k(n, adj, 2)
            fails = 0
        else:
            for a, b in added:
                eset.discard((a, b) if a < b else (b, a))
                adj[a].discard(b)
                adj[b].discard(a)
            adj.pop()
            adj.pop()
            color.pop()
            color.pop()
            fails += 1
    return n, sorted(eset)


# ----------------------------------------------------------------------------
# Edge-split growth ("swap-grow").
#
# When plain cover extension saturates, every vertex with spare degree is
# unusable as a cover. A swap move takes a saturated vertex s and one of its
# neighbours t, deletes the edge (s, t) and inserts a new vertex x on t's side
# adjacent to s plus a fresh cover set of spare vertices on s's side. The
# deletion frees one slot at t, so the move is a net +1 vertex. Every move is
# checked with lib.is_valid and reverted on failure.
# ----------------------------------------------------------------------------

def _swap_grow(n, edges, d, D, deadline, rng):
    """Grow by edge-split moves until the deadline; return (n, edges), always valid."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, adj)

    while time.monotonic() < deadline:
        sat = [v for v in range(n) if len(adj[v]) == d]
        if not sat:
            break
        s = rng.choice(sat)
        t = rng.choice(sorted(adj[s]))
        key = (s, t) if s < t else (t, s)
        eset.discard(key)
        adj[s].discard(t)
        adj[t].discard(s)

        reach = _ball3(n, adj)
        unc = ((1 << n) - 1) & ~reach[s]
        pool = [v for v in range(n) if color[v] == color[s] and v != s and len(adj[v]) < d]
        S = [s]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)

        if unc == 0:
            x = n
            adj.append(set())
            color.append(color[t])
            for w in S:
                adj[w].add(x)
                adj[x].add(w)
                eset.add((w, x))
            if lib.is_valid(n + 1, list(eset), d, D):
                n += 1
                continue
            # Revert the new vertex.
            for w in S:
                adj[w].discard(x)
                eset.discard((w, x))
            adj.pop()
            color.pop()

        # Restore the removed edge.
        adj[s].add(t)
        adj[t].add(s)
        eset.add(key)
    return n, sorted(eset)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.4 * budget
    extend_deadline = t0 + 0.6 * budget
    pair_deadline = t0 + 0.8 * budget
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

    # Twin graph on W(d-2), cover extension, paired growth, then edge-split growth.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, extend_deadline, rng)
            consider(n3, e3)
            if lib.is_valid(n3, e3, d, D):
                n5, e5 = _pair_grow(n3, e3, d, D, pair_deadline, rng)
            else:
                n5, e5 = n3, e3
            consider(n5, e5)
            if lib.is_valid(n5, e5, d, D):
                n4, e4 = _swap_grow(n5, e5, d, D, deadline, rng)
                consider(n4, e4)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
