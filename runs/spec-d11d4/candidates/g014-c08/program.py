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
# Returns (n, edges, side) where side[v] in {0, 1} is a bipartition class.
# ----------------------------------------------------------------------------

def _twin_graph(q, i_deadline, j_deadline, rng):
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

    I = _mis(P, [sorted(s) for s in padj], i_deadline, rng)
    J = _mis(L, [sorted(s) for s in ladj], j_deadline, rng)

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
# NEW: spare-slot augmentation by 2-domination set cover.
#
# A new vertex x on side s with neighbour set N (all on side 1-s) keeps the
# diameter at 4 exactly when every vertex w of side 1-s lies within distance 2
# of some u in N. Every other pair is automatically fine: the existing graph is
# bipartite with diameter 4, so cross-side distances are odd and at most 3,
# and x reaches side-s vertices via any neighbour. Each candidate's radius-2
# ball is a bitmask, so the choice of N is a greedy bitset set cover over
# spare vertices of side 1-s.
# ----------------------------------------------------------------------------

def _augment(n, edges, side, d, deadline, rng):
    nb = [0] * n
    adjl = [[] for _ in range(n)]
    deg = [0] * n
    for u, v in edges:
        nb[u] |= 1 << v
        nb[v] |= 1 << u
        adjl[u].append(v)
        adjl[v].append(u)
        deg[u] += 1
        deg[v] += 1
    side = list(side)
    edges = list(edges)
    masks = [0, 0]
    for v in range(n):
        masks[side[v]] |= 1 << v

    def ball2(u):
        b = (1 << u) | nb[u]
        for v in adjl[u]:
            b |= nb[v]
        return b

    def try_add(s):
        t = 1 - s
        target = masks[t]
        cands = [u for u in range(n) if side[u] == t and deg[u] < d]
        if not cands:
            return None
        rng.shuffle(cands)
        balls = {u: ball2(u) & target for u in cands}
        covered = 0
        chosen = []
        used = set()
        while covered != target and len(chosen) < d:
            best, bestg = -1, 0
            for u in cands:
                if u in used:
                    continue
                g = (balls[u] & ~covered).bit_count()
                if g > bestg:
                    best, bestg = u, g
            if best < 0:
                return None
            used.add(best)
            chosen.append(best)
            covered |= balls[best]
        return chosen if covered == target else None

    fails = 0
    while time.monotonic() < deadline and fails < 40:
        order = [0, 1]
        rng.shuffle(order)
        done = False
        for s in order:
            chosen = try_add(s)
            if chosen:
                x = n
                n += 1
                side.append(s)
                nb.append(0)
                adjl.append([])
                deg.append(0)
                masks[s] |= 1 << x
                for u in chosen:
                    edges.append((u, x))
                    nb[u] |= 1 << x
                    nb[x] |= 1 << u
                    adjl[u].append(x)
                    adjl[x].append(u)
                    deg[u] += 1
                    deg[x] += 1
                done = True
                fails = 0
                break
        if not done:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 10.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            P, lines = _gq_w(d - 1)
            n = P + len(lines)
            e = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(n, e)
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n, edges, side = _twin_graph(d - 2, t0 + 0.4 * total, t0 + 0.75 * total, rng)
            consider(n, edges)
            try:
                n2, e2 = _augment(n, edges, side, d, t0 + total, rng)
                consider(n2, e2)
            except Exception:
                pass
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
