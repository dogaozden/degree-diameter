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
# New construction: bipartite lifts over NON-ABELIAN groups.
#
# Base graph: kb vertices on side A (ids 0..kb-1) and kb on side B (ids kb..2kb-1).
# Every A-vertex carries exactly d darts; each dart (a -> c, g) joins (a, x) to
# (c, x*g) for all x in G = Z_m x| Z_k (lib.semidirect_group). Left multiplication
# by h is an automorphism, so diameter <= D holds iff each base vertex's identity
# copy reaches everything within D steps. Hill climbing moves dart elements and
# swaps dart targets (which keeps every B-side degree equal to d).
# ----------------------------------------------------------------------------

def _group_options(N):
    """All (m, k, r) with m*k = N, m >= 2, defining a valid semidirect product Z_m x| Z_k."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _unreached(adj, N, nb, b0, D):
    """Number of lifted vertices not within D steps of the identity copy of base vertex b0."""
    total = nb * N
    seen = bytearray(total)
    s = b0 * N
    seen[s] = 1
    frontier = [s]
    reached = 1
    for _ in range(D):
        nxt = []
        app = nxt.append
        for v in frontier:
            b, x = divmod(v, N)
            for off, R in adj[b]:
                w = off + R[x]
                if not seen[w]:
                    seen[w] = 1
                    app(w)
        if not nxt:
            break
        reached += len(nxt)
        frontier = nxt
    return total - reached


def _bilift_search(d, D, kb, N, deadline, rng):
    """Hill-climb a group lift on 2*kb*N vertices; return (n, edges) or None before deadline."""
    nb = 2 * kb
    opts = _group_options(N)
    if not opts:
        return None
    nonab = [o for o in opts if o[1] > 1 and o[2] != 1]

    def new_group():
        if nonab and rng.random() < 0.8:
            m, k, r = rng.choice(nonab)
        else:
            m, k, r = rng.choice(opts)
        _, mul, inv = lib.semidirect_group(m, k, r)
        ginv = [inv(x) for x in range(N)]
        cache = {}

        def R(g):
            t = cache.get(g)
            if t is None:
                if len(cache) > 3000:
                    cache.clear()
                t = [mul(x, g) for x in range(N)]
                cache[g] = t
            return t

        return R, ginv

    def fresh_darts():
        pool = [c for c in range(kb) for _ in range(d)]
        rng.shuffle(pool)
        tgt = [pool[a * d:(a + 1) * d] for a in range(kb)]
        gel = [[rng.randrange(N) for _ in range(d)] for _ in range(kb)]
        return tgt, gel

    def score(tgt, gel, R, ginv, limit):
        adj = [[] for _ in range(nb)]
        for a in range(kb):
            ta, ga = tgt[a], gel[a]
            for i in range(d):
                c = kb + ta[i]
                g = ga[i]
                adj[a].append((c * N, R(g)))
                adj[c].append((a * N, R(ginv[g])))
        total = 0
        for b0 in range(nb):
            total += _unreached(adj, N, nb, b0, D)
            if total > limit:
                return total
        return total

    R, ginv = new_group()
    tgt, gel = fresh_darts()
    cur = score(tgt, gel, R, ginv, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            R, ginv = new_group()
            tgt, gel = fresh_darts()
            cur = score(tgt, gel, R, ginv, 1 << 60)
            stall = 0
            continue
        if rng.random() < 0.5:
            a = rng.randrange(kb)
            i = rng.randrange(d)
            old = gel[a][i]
            gel[a][i] = rng.randrange(N)
            new = score(tgt, gel, R, ginv, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                gel[a][i] = old
        else:
            a = rng.randrange(kb)
            i = rng.randrange(d)
            a2 = rng.randrange(kb)
            i2 = rng.randrange(d)
            if tgt[a][i] == tgt[a2][i2]:
                continue
            tgt[a][i], tgt[a2][i2] = tgt[a2][i2], tgt[a][i]
            new = score(tgt, gel, R, ginv, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                tgt[a][i], tgt[a2][i2] = tgt[a2][i2], tgt[a][i]

    E = set()
    for a in range(kb):
        for i in range(d):
            c = kb + tgt[a][i]
            Rg = R(gel[a][i])
            for x in range(N):
                E.add((a * N + x, c * N + Rg[x]))
    return 2 * kb * N, sorted(E)


def _new_phase(d, D, best_n, deadline, rng, consider):
    """Repeatedly search group lifts of order above the current best until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    cur = best_n
    while time.monotonic() < deadline and cur < moore:
        order_pref = [2, 1, 3] if rng.random() < 0.6 else [1, 2, 3]
        kb = None
        for c in order_pref:
            if 2 * c * (cur // (2 * c) + 1) <= moore:
                kb = c
                break
        if kb is None:
            break
        N = cur // (2 * kb) + 1
        now = time.monotonic()
        slice_end = min(deadline, now + max(4.0, (deadline - now) / 3.0))
        res = _bilift_search(d, D, kb, N, slice_end, rng)
        if res is not None:
            n, edges = res
            if n > cur and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                cur = n


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.4 * budget
    twin_deadline = t0 + 0.3 * budget
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

    # New construction: non-abelian group lifts of small bipartite base graphs.
    if D >= 2 and d >= 2:
        try:
            _new_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
