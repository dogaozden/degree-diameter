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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n          # number of neighbours of v inside S
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# Returns (n, edges, side) where side[v] = 0 for point-side and 1 for line-side
# vertices (bipartition classes). Point twins are point-side, line twins line-side.
# ----------------------------------------------------------------------------

def _twin_graph(q, dI, dJ, rng):
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

    I = _mis(P, [sorted(s) for s in padj], dI, rng)
    J = _mis(L, [sorted(s) for s in ladj], dJ, rng)

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
# New helper: radius-3 cover extension.
#
# In a diameter-D graph, a new vertex x adjacent to a set S reaches every
# vertex v within D iff some s in S has dist(s, v) <= D - 1. So we pick the
# neighbours of x as a greedy cover of all existing vertices by radius-(D-1)
# balls, using only vertices with spare degree on the opposite side. Each new
# vertex is verified with lib.is_valid and reverted if it fails.
# ----------------------------------------------------------------------------

def _ball(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _extend(n, edges, side, d, D, deadline, rng):
    """Greedily add vertices via radius-(D-1) cover; return a verified (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = list(side)
    E = list(edges)
    cur_n = n
    fails = 0
    t = 0
    while time.monotonic() < deadline and fails < 6:
        tt = t
        t ^= 1
        ball = _ball(cur_n, adj, D - 1)
        full = (1 << cur_n) - 1
        cands = [c for c in range(cur_n) if side[c] == 1 - tt and len(adj[c]) < d]
        rng.shuffle(cands)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and cands:
            bc, bg, bi = -1, 0, -1
            for i, c in enumerate(cands):
                g = (ball[c] & ~covered).bit_count()
                if g > bg:
                    bg, bc, bi = g, c, i
            if bg == 0:
                break
            chosen.append(bc)
            covered |= ball[bc]
            cands[bi] = cands[-1]
            cands.pop()
        if covered != full:
            fails += 1
            continue
        x = cur_n
        len0 = len(E)
        for c in chosen:
            adj[c].append(x)
            E.append((c, x))
        adj.append(list(chosen))
        side.append(tt)
        if lib.is_valid(cur_n + 1, E, d, D):
            cur_n += 1
            fails = 0
        else:
            for c in chosen:
                adj[c].pop()
            adj.pop()
            side.pop()
            del E[len0:]
            fails += 1
    return cur_n, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Twins on W(d-2) plus radius-cover extension (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            dI = t0 + 0.25 * budget
            dJ = t0 + 0.5 * budget
            n, edges, side = _twin_graph(d - 2, dI, dJ, rng)
            consider(n, edges)
            n2, e2 = _extend(n, edges, side, d, D, deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
