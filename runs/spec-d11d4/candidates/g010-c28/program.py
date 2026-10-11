import itertools
import math
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
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

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

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
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
# NEW: Haar graph search for diameter 4.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S (|S| = d, S subset of Z_m).
# Z_m acts by translation on both sides, so diameter <= 4 holds iff every
# vertex is within distance 4 of a_0 and within distance 4 of b_0. The score
# counts vertices missed by those two balls; score 0 means a valid graph.
# We run simulated annealing on S (0 kept fixed by translation symmetry).
# ----------------------------------------------------------------------------

def _reach_missing(S, m, side):
    """Number of vertices NOT within distance 4 of the source vertex 0 on the given side (0 = A, 1 = B)."""
    seen = (bytearray(m), bytearray(m))
    seen[side][0] = 1
    front = [(side, 0)]
    for _ in range(4):
        nxt = []
        for t, x in front:
            if t == 0:
                for s in S:
                    y = (x + s) % m
                    if not seen[1][y]:
                        seen[1][y] = 1
                        nxt.append((1, y))
            else:
                for s in S:
                    y = (x - s) % m
                    if not seen[0][y]:
                        seen[0][y] = 1
                        nxt.append((0, y))
        front = nxt
        if not front:
            break
    return (m - sum(seen[0])) + (m - sum(seen[1]))


def _score(S, m):
    """Total missed vertices from a_0 and from b_0; zero iff the Haar graph has diameter <= 4."""
    return _reach_missing(S, m, 0) + _reach_missing(S, m, 1)


def _haar_search(m, d, deadline, rng):
    """Anneal a connection set S of size d in Z_m so that H(m, S) has diameter 4; return S or None."""
    if m < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _score(S, m)
    best_s, best_v = list(S), cur
    T = 1.5
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(1, d)
        r = rng.randrange(1, m)
        if r in S:
            continue
        old = S[i]
        S[i] = r
        new = _score(S, m)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            if cur < best_v:
                best_v, best_s = cur, list(S)
        else:
            S[i] = old
        if it % 2000 == 0:
            T = max(0.2, T * 0.85)
    return best_s if best_v == 0 else None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.4 * budget
    twin_deadline = t0 + 0.2 * budget
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

    # Twin graph on W(d-2), then greedy set-cover extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # NEW: Haar graphs H(m, S) over Z_m, searched by annealing, for diameter 4.
    # Each success is a fresh, larger order; we keep going while time remains.
    if D == 4 and d >= 3:
        try:
            m = best[0] // 2 + 1
            while time.monotonic() < deadline:
                now = time.monotonic()
                remaining = deadline - now
                sub = min(deadline, now + max(3.0, 0.5 * remaining))
                S = _haar_search(m, d, sub, rng)
                if S is None:
                    break
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                m += 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
