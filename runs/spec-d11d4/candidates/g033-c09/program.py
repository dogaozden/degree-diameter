import itertools
import random
import time
from math import gcd

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
# Bold new construction: lifts over NON-abelian semidirect groups Z_m x| Z_kk.
#
# Base graph: k vertices on side A (ids 0..k-1) and k on side B (ids k..2k-1).
# Layer i (i < d) is a bijection u -> k + perm_i[u], with a group element
# elem_i[u] attached to the dart. The lift has vertices (b, x), x in the group,
# id b*G + x, and edge (u, x) -- (k+perm_i[u], x * elem_i[u]).
# Every A-vertex has d darts and every B-vertex receives exactly d darts, so
# max degree is d and the lift is bipartite.
#
# Left multiplication by a group element is an automorphism, so it suffices to
# BFS from (b, identity) for each base vertex b. The search minimises the number
# of unreached pairs by hill climbing, and accepts only zero-defect lifts that
# also pass lib.is_valid.
# ----------------------------------------------------------------------------

def _semidirect_table(m, kk, r):
    """Multiplication table of Z_m x|_r Z_kk, element (a, b) coded a*kk+b; identity is 0."""
    G = m * kk
    pw = [pow(r, b, m) for b in range(kk)]
    mt = [[0] * G for _ in range(G)]
    for x in range(G):
        a1, b1 = divmod(x, kk)
        row = mt[x]
        for y in range(G):
            c, d2 = divmod(y, kk)
            row[y] = ((a1 + pw[b1] * c) % m) * kk + (b1 + d2) % kk
    inv = [row.index(0) for row in mt]
    return mt, inv


def _groups_of_order(G):
    """Return (m, kk, r) triples describing semidirect groups Z_m x|_r Z_kk of order G."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        kk = G // m
        rs = [0] if m == 1 else range(1, m)
        for r in rs:
            if gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _grp_adj(k, d, perm, elem, inv):
    """Base adjacency: adj[b] = list of (neighbour base id, group element h) for the dart action x -> x*h."""
    adj = [[] for _ in range(2 * k)]
    for i in range(d):
        p = perm[i]
        e = elem[i]
        for u in range(k):
            v = k + p[u]
            h = e[u]
            adj[u].append((v, h))
            adj[v].append((u, inv[h]))
    return adj


def _grp_score(k, G, mt, adj, D, limit):
    """Total number of (source, vertex) pairs not reached within D steps; stops once above limit."""
    N = 2 * k * G
    total = 0
    for b0 in range(2 * k):
        seen = bytearray(N)
        s0 = b0 * G
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for z in frontier:
                b, x = divmod(z, G)
                mrow = mt[x]
                for nb, h in adj[b]:
                    y = nb * G + mrow[h]
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
        if total > limit:
            return total
    return total


def _grp_edges(k, d, G, mt, perm, elem):
    """Return (n, edges) for the lift described by perm and elem."""
    E = set()
    for i in range(d):
        for u in range(k):
            v = k + perm[i][u]
            h = elem[i][u]
            for x in range(G):
                a = u * G + x
                b = v * G + mt[x][h]
                E.add((a, b) if a < b else (b, a))
    return 2 * k * G, sorted(E)


def _grp_search(d, k, G, mt, inv, D, deadline, rng):
    """Hill-climb a lift on 2*k*G vertices; return (n, edges) or None."""

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        elem = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        return perm, elem

    def evaluate(perm, elem, limit):
        return _grp_score(k, G, mt, _grp_adj(k, d, perm, elem, inv), D, limit)

    perm, elem = fresh()
    cur = evaluate(perm, elem, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            perm, elem = fresh()
            cur = evaluate(perm, elem, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(k)
        if rng.random() < 0.6:
            old = elem[i][u]
            elem[i][u] = rng.randrange(G)
            new = evaluate(perm, elem, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                elem[i][u] = old
        else:
            u2 = rng.randrange(k)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = evaluate(perm, elem, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return _grp_edges(k, d, G, mt, perm, elem)


def _grp_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search semidirect-product lifts of order above bn until the deadline or the Moore bound."""
    if d < 2 or D < 2:
        return bn
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        ks = [kb for kb in (2, 3, 4) if 2 * kb * (bn // (2 * kb) + 1) <= moore]
        if not ks:
            break
        kb = rng.choice(ks)
        gmin = bn // (2 * kb) + 1
        G = gmin + rng.randrange(4)
        if 2 * kb * G > moore:
            G = gmin
        opts = _groups_of_order(G)
        if not opts:
            continue
        m, kk, r = rng.choice(opts)
        mt, inv = _semidirect_table(m, kk, r)
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, (deadline - now) / 4.0))
        res = _grp_search(d, kb, G, mt, inv, D, slice_end, rng)
        if res is not None:
            n, edges = res
            if n > bn and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                bn = n
    return bn


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.45 * budget
    twin_deadline = t0 + 0.30 * budget
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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold stage: lifts over semidirect products Z_m x| Z_kk of small base graphs.
    if D >= 2 and d >= 2:
        try:
            _grp_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
