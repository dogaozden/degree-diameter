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
    c = [0] * n
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
# BOLD CONSTRUCTION: start from the incidence graph of W(q) (degree q+1, order
# 2(q+1)(q^2+1)) and delete two vertex sets:
#   S: lines that together cover every point (so each remaining point loses a neighbour);
#   O: points that together hit every line not in S (so each remaining line loses a neighbour).
# Every surviving vertex then has degree <= q = d. Distance-4 is not guaranteed,
# so a greedy repair deletes the vertices that leave the most pairs too far apart
# until the graph has diameter <= 4. The result is then extended with _extend.
# ----------------------------------------------------------------------------

def _bold_q(q, target_n, deadline, rng):
    """Return (n, edges) of a valid degree-q, diameter-4 bipartite graph with n >= target_n, or None."""
    P, lines = _gq_w(q)
    L = len(lines)
    line_mask = []
    for Ls in lines:
        m = 0
        for p in Ls:
            m |= 1 << p
        line_mask.append(m)
    pt_mask = [0] * P
    for j, Ls in enumerate(lines):
        bit = 1 << j
        for p in Ls:
            pt_mask[p] |= bit

    # Phase 1: greedy cover of all points by lines (set S, to be removed).
    unc = (1 << P) - 1
    S = set()
    order = list(range(L))
    while unc:
        rng.shuffle(order)
        bj, bg = -1, 0
        for j in order:
            g = (line_mask[j] & unc).bit_count()
            if g > bg:
                bg, bj = g, j
        if bj < 0:
            break
        S.add(bj)
        unc &= ~line_mask[bj]

    # Phase 2: greedy hitting of all lines not in S by points (set O, to be removed).
    unhit = 0
    for j in range(L):
        if j not in S:
            unhit |= 1 << j
    O = set()
    porder = list(range(P))
    while unhit:
        rng.shuffle(porder)
        bp, bg = -1, 0
        for p in porder:
            g = (pt_mask[p] & unhit).bit_count()
            if g > bg:
                bg, bp = g, p
        if bp < 0:
            break
        O.add(bp)
        unhit &= ~pt_mask[bp]

    # Build the surviving graph. Vertex ids: points 0..P-1, lines P..P+L-1.
    N = P + L
    adj = [set() for _ in range(N)]
    for j, Ls in enumerate(lines):
        if j in S:
            continue
        for p in Ls:
            if p in O:
                continue
            adj[p].add(P + j)
            adj[P + j].add(p)
    alive = [False] * N
    for p in range(P):
        if p not in O:
            alive[p] = True
    for j in range(L):
        if j not in S:
            alive[P + j] = True

    # Repair: delete the vertices that leave the most pairs at distance > 4.
    while True:
        if time.monotonic() > deadline:
            return None
        av = [v for v in range(N) if alive[v]]
        na = len(av)
        if na < target_n:
            return None
        reach = [0] * N
        for v in av:
            reach[v] = 1 << v
        for _ in range(4):
            new = list(reach)
            for v in av:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
            reach = new
        bad = [(na - reach[v].bit_count(), v) for v in av]
        if all(b == 0 for b, _ in bad):
            break
        bad.sort(reverse=True)
        k = max(1, na // 150)
        changed = False
        for b, v in bad[:k]:
            if b <= 0:
                break
            alive[v] = False
            for u in adj[v]:
                adj[u].discard(v)
            adj[v] = set()
            changed = True
        if not changed:
            return None

    edges = []
    for v in av:
        for u in adj[v]:
            if v < u:
                edges.append((v, u))
    if not edges:
        return None
    n, edges = lib.relabel(edges)
    if n < target_n:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Randomized greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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

    spare = [v for v in range(n) if len(adj[v]) < d]

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
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
            spare = [v for v in spare if len(adj[v]) < d]
            if len(S) < d:
                spare.append(x)
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    # The parent pipeline keeps its original twin-MIS window and ends at pdeadline;
    # the bold construction gets the remaining time.
    pdeadline = t0 + 0.6 * budget
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

    # Parent pipeline: twin graph on W(d-2), then randomized set-cover extensions.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= pdeadline - 0.5:
                    break
                slice_end = now + (pdeadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, pdeadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    # BOLD: W(d) minus a line cover and a point hitting set (degree d), then repair
    # to diameter 4 and extend. Only attempted when it can beat the current best.
    if D >= 4 and lib.is_prime_power(d) and 3 <= d <= 11:
        try:
            res = _bold_q(d, best[0] + 1, t0 + 0.92 * budget, rng)
            if res is not None:
                consider(*res)
                n5, e5 = _extend(res[0], res[1], d, deadline, rng)
                consider(n5, e5)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
