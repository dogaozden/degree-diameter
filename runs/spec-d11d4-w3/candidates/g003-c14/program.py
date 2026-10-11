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
# Set-cover vertex extension (diameter 4).
#
# A new vertex x joined to S (opposite side, spare degree) keeps diameter <= 4
# iff the union of R3(s) over s in S covers every current vertex. The reach
# sets are recomputed after every addition, so new vertices are also covered.
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
    while time.monotonic() < deadline and fails < 100:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
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
        fails = 0
        x = n
        n += 1
        for s in S:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
    return n, edges


# ----------------------------------------------------------------------------
# New family: W(d) incidence graph (degree d+1), delete a dominating set so every
# survivor has degree <= d, repair remaining diameter violations by deleting the
# worst vertices, then extend with the set-cover method.
# ----------------------------------------------------------------------------

def _dominate(n, adj, rng):
    """Random greedy set T so every vertex is in T or adjacent to T. Returns inT flags."""
    inT = [False] * n
    dom = [False] * n
    order = list(range(n))
    rng.shuffle(order)
    for u in order:
        if dom[u]:
            continue
        best, bg = u, -1
        for t in [u] + adj[u]:
            g = 0 if dom[t] else 1
            for w in adj[t]:
                if not dom[w]:
                    g += 1
            if g > bg:
                best, bg = t, g
        inT[best] = True
        dom[best] = True
        for w in adj[best]:
            dom[w] = True
    return inT


def _repair(alive, edges, deadline, rng):
    """Delete high-bad-pair vertices until diameter <= 4 holds. Returns (m, edges) or None on timeout."""
    alive = set(alive)
    while True:
        if time.monotonic() > deadline:
            return None
        order = sorted(alive)
        m = len(order)
        if m == 0:
            return 0, []
        idx = {v: i for i, v in enumerate(order)}
        ce = [(idx[u], idx[v]) for u, v in edges if u in alive and v in alive]
        reach = lib._balls(m, ce, 4)
        bad = [m - r.bit_count() for r in reach]
        if sum(bad) == 0:
            return m, ce
        k = max(1, m // 150)
        keys = [(-bad[i], rng.random(), i) for i in range(m)]
        keys.sort()
        removed = 0
        for _, _, i in keys:
            if removed >= k or bad[i] == 0:
                break
            alive.discard(order[i])
            removed += 1


def _deleted_pipeline(d, deadline, rng, consider):
    """Build W(d) incidence (degree d+1), reduce to degree d by deletion, repair, then extend."""
    if time.monotonic() > deadline - 5.0:
        return
    n, edges = _gq_incidence(d)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    now = time.monotonic()
    rep_dl = now + (deadline - now) * 0.6
    inT = _dominate(n, adj, rng)
    alive = [v for v in range(n) if not inT[v]]
    rep = _repair(alive, edges, rep_dl, rng)
    if rep is None:
        return
    m, ce = rep
    consider(m, ce)
    n2, e2 = _extend(m, ce, d, deadline, rng)
    consider(n2, e2)


# ----------------------------------------------------------------------------
# Parent pipeline: twin graph on W(q), q = d-2, then set-cover extension.
# ----------------------------------------------------------------------------

def _parent_pipeline(q, d, deadline, rng, consider):
    attempt = 0
    while attempt < 4:
        now = time.monotonic()
        rem = deadline - now
        if rem < 3.0:
            break
        share = rem if attempt == 3 else rem * 0.5
        tw_dl = now + share * 0.4
        ex_dl = now + share
        try:
            n2, e2 = _twin_graph(q, tw_dl, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, ex_dl, rng)
            consider(n3, e3)
        except Exception:
            pass
        attempt += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    if D >= 4:
        now = time.monotonic()
        split = now + (deadline - now) * 0.4

        # Parent-style twin construction (about 40% of the budget).
        if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                _parent_pipeline(d - 2, d, split, rng, consider)
            except Exception:
                pass

        # Bold new family: deletion from W(d) with repair and extension (rest of budget).
        if lib.is_prime_power(d) and 3 <= d <= 13:
            try:
                _deleted_pipeline(d, deadline, rng, consider)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
