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
    """Incidence graph of W(q): (n, edges), degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph found before deadline."""
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
# NEW (bold) construction: bipartite lifts over NON-cyclic groups.
#
# Base graph: bk vertices on side A (0..bk-1) and bk on side B (bk..2bk-1),
# d dart-matchings, each dart (u, perm[i][u], volt[i][u]) with voltage a
# group element. The group is Z_m x|_r Z_gk (semidirect product), so it can
# be nonabelian. Lift vertex (b, x) has id b*N + x and (u, x) ~ (v, x*g) for
# every dart (u, v, g). Left multiplication is an automorphism, so the
# diameter check only needs BFS from (b, identity) for each base vertex.
# The search hill-climbs voltages and matchings to zero unreached pairs.
# ----------------------------------------------------------------------------

def _grp_adj(bk, perm, volt, ginv):
    """Base adjacency: adj[b] = list of (neighbour base id, group element to right-multiply by)."""
    adj = [[] for _ in range(2 * bk)]
    for i in range(len(perm)):
        p = perm[i]
        vo = volt[i]
        for u in range(bk):
            w = p[u]
            g = vo[u]
            adj[u].append((bk + w, g))
            adj[bk + w].append((u, ginv(g)))
    return adj


def _grp_score(bk, N, adj, D, gmul, limit):
    """Total unreached (source, vertex) pairs within D steps from each base vertex at identity; early stop above limit."""
    tot = 2 * bk * N
    total = 0
    for b0 in range(2 * bk):
        seen = bytearray(tot)
        s0 = b0 * N
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for z in frontier:
                b, x = divmod(z, N)
                for nb, g in adj[b]:
                    y = nb * N + gmul(x, g)
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += tot - reached
        if total > limit:
            return total
    return total


def _grp_edges(bk, N, adj, gmul):
    """Return (n, edges) of the lift."""
    E = set()
    for b in range(bk):
        for x in range(N):
            for nb, g in adj[b]:
                a = b * N + x
                c = nb * N + gmul(x, g)
                if a != c:
                    E.add((min(a, c), max(a, c)))
    return 2 * bk * N, sorted(E)


def _grp_search(d, D, bk, N, gmul, ginv, slice_end, rng):
    """Hill-climb a valid lift on 2*bk*N vertices; return (n, edges) or None."""

    def fresh():
        perm = [rng.sample(range(bk), bk) for _ in range(d)]
        volt = [[rng.randrange(N) for _ in range(bk)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _grp_score(bk, N, _grp_adj(bk, perm, volt, ginv), D, gmul, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > slice_end:
            return None
        stall += 1
        if stall > 300:
            perm, volt = fresh()
            cur = _grp_score(bk, N, _grp_adj(bk, perm, volt, ginv), D, gmul, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(bk)
        if bk == 1 or rng.random() < 0.7:
            old = volt[i][u]
            volt[i][u] = rng.randrange(N)
            new = _grp_score(bk, N, _grp_adj(bk, perm, volt, ginv), D, gmul, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(bk)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _grp_score(bk, N, _grp_adj(bk, perm, volt, ginv), D, gmul, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return _grp_edges(bk, N, _grp_adj(bk, perm, volt, ginv), gmul)


def _pick_group(lo, hi, rng):
    """Random semidirect product Z_m x|_r Z_gk with order m*gk in [lo, hi]; return (m, gk, r) or None."""
    for _ in range(200):
        gk = rng.choice([2, 3, 4, 5, 6])
        mlo = max(2, lo // gk)
        mhi = max(mlo, hi // gk)
        if mlo > mhi:
            continue
        m = rng.randint(mlo, mhi)
        N = m * gk
        if N < lo or N > hi:
            continue
        for _ in range(60):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, gk, m) == 1 % m:
                return m, gk, r
    return None


def _grp_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search non-cyclic group lifts of order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        options = []
        for bk in (1, 2, 3):
            lo = bn // (2 * bk) + 1
            hi = min(moore // (2 * bk), lo + max(4, lo // 4))
            if lo <= hi:
                options.append((bk, lo, hi))
        if not options:
            break
        bk, lo, hi = rng.choice(options)
        grp = _pick_group(lo, hi, rng)
        if grp is None:
            continue
        m, gk, r = grp
        N, gmul, ginv = lib.semidirect_group(m, gk, r)
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, (deadline - now) / 3.0))
        res = _grp_search(d, D, bk, N, gmul, ginv, slice_end, rng)
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

    # Twin graph on W(d-2), then randomized set-cover extension (baseline that beats the record for d=11, D=4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold new search: bipartite lifts over non-cyclic semidirect product groups.
    if D >= 2 and d >= 2:
        try:
            _grp_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
