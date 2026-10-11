import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent pipeline (kept as the strong baseline): W(q) incidence, twin graph,
# cover extension and edge-split growth.
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


def _mis(n, adj, deadline, rng):
    """Return a large independent set found before deadline (tabu search)."""
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


NOISE = 0.25


def _ball3(n, adj):
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


def _extend(n, edges, d, deadline, rng):
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


def _swap_grow(n, edges, d, D, deadline, rng):
    """Grow by edge-split moves until the deadline; always returns a valid graph."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, [sorted(s) for s in adj])

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

        reach = _ball3(n, [sorted(x) for x in adj])
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
            for w in S:
                adj[w].discard(x)
                eset.discard((w, x))
            adj.pop()
            color.pop()

        adj[s].add(t)
        adj[t].add(s)
        eset.add(key)
    return n, sorted(eset)


# ----------------------------------------------------------------------------
# NEW construction: voltage lifts over small (possibly non-abelian) groups.
#
# Base graph: k vertices on side A and k on side B, d darts per base vertex
# (d random perfect matchings between sides). Each dart carries a voltage g in
# a group G of order M; the lift has 2*k*M vertices, is bipartite, and has
# degree d. Left translation is an automorphism, so the diameter is <= D iff
# every base vertex, as a source (u, e), reaches the whole lift within D steps.
# Voltages are improved by a hill climb on the number of unreached pairs.
# ----------------------------------------------------------------------------

def _random_group(M, rng):
    """Return (m, kk, r) describing Z_m x| Z_kk of order M (kk=1 means cyclic)."""
    divs = [kk for kk in range(1, M + 1) if M % kk == 0 and M // kk >= 2]
    kk = rng.choice(divs)
    m = M // kk
    if kk > 1 and m >= 3:
        for _ in range(300):
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                return m, kk, r
    return M, 1, 1


def _tables(m, kk, r):
    """Multiplication table (numpy), its transpose, and inverse table for Z_m x| Z_kk."""
    M = m * kk
    xs = np.arange(M, dtype=np.int64)
    a = xs // kk
    b = xs % kk
    pw = np.array([pow(r, j, m) for j in range(kk)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % kk
    mt = A * kk + B
    invtab = np.argmax(mt == 0, axis=1).astype(np.int64)
    MT_T = np.ascontiguousarray(mt.T)
    return mt, MT_T, invtab


def _cost(src, dst, h, k2, M, D, MT_T):
    """Total number of (source base vertex, lifted vertex) pairs at distance > D."""
    total = 0
    E2 = len(src)
    for s in range(k2):
        reached = np.zeros((k2, M), dtype=bool)
        reached[s, 0] = True
        cur = reached.copy()
        for _ in range(D):
            nxt = np.zeros((k2, M), dtype=bool)
            for e in range(E2):
                nxt[dst[e], MT_T[h[e]]] |= cur[src[e]]
            cur = nxt & ~reached
            if not cur.any():
                break
            reached |= cur
        total += k2 * M - int(reached.sum())
    return total


def _climb(us, vs, k2, M, D, MT_T, invtab, deadline, rng):
    """Hill-climb voltages; return (best_cost, best_voltages)."""
    E = len(us)
    src = list(us) + list(vs)
    dst = list(vs) + list(us)

    def full(g):
        h = np.concatenate([g, invtab[g]])
        return _cost(src, dst, h, k2, M, D, MT_T)

    g = np.array([rng.randrange(M) for _ in range(E)], dtype=np.int64)
    c = full(g)
    bestc, bestg = c, g.copy()
    stale = 0
    while bestc > 0 and time.monotonic() < deadline:
        i = rng.randrange(E)
        old = int(g[i])
        g[i] = rng.randrange(M)
        nc = full(g)
        if nc <= c or rng.random() < 0.01:
            c = nc
        else:
            g[i] = old
        if c < bestc:
            bestc, bestg, stale = c, g.copy(), 0
        else:
            stale += 1
        if stale > 3000:
            g = np.array([rng.randrange(M) for _ in range(E)], dtype=np.int64)
            c = full(g)
            stale = 0
    return bestc, bestg


def _lift_search(d, D, moore, deadline, rng, best_n, consider):
    """Repeatedly try voltage lifts of larger order; call consider() on each valid success."""
    while time.monotonic() < deadline:
        cands = []
        for k in range(1, 7):
            lo = best_n // (2 * k) + 1
            hi = moore // (2 * k)
            for M in range(lo, hi + 1):
                cands.append((2 * k * M, k, M))
        if not cands:
            return
        cands.sort()
        n_t, k, M = rng.choice(cands[:40])
        remaining = deadline - time.monotonic()
        if remaining <= 0.2:
            return
        slice_end = time.monotonic() + min(remaining, max(2.0, remaining / 4))

        m, kk, r = _random_group(M, rng)
        mt, MT_T, invtab = _tables(m, kk, r)

        us, vs = [], []
        for _ in range(d):
            perm = list(range(k))
            rng.shuffle(perm)
            for u in range(k):
                us.append(u)
                vs.append(k + perm[u])

        c, g = _climb(us, vs, 2 * k, M, D, MT_T, invtab, slice_end, rng)
        if c == 0:
            darts = [(us[i], vs[i], int(g[i])) for i in range(len(us))]
            mulf = lambda x, y, mt=mt: int(mt[x, y])
            n, edges = lib.group_lift(2 * k, darts, M, mulf)
            if n > best_n and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                best_n = n


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

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    moore = lib.moore_bound(d, D)

    # Parent pipeline gets 60% of the budget.
    tp = time.monotonic()
    pb = 0.6 * budget
    twin_deadline = tp + 0.4 * pb
    extend_deadline = tp + 0.7 * pb
    pdeadline = tp + pb

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, extend_deadline, rng)
            consider(n3, e3)
            n4, e4 = _swap_grow(n3, e3, d, D, pdeadline, rng)
            consider(n4, e4)
        except Exception:
            pass

    # Remaining time: voltage-lift search for orders above the current best.
    if best[0] < moore and D >= 2 and d >= 3:
        try:
            _lift_search(d, D, moore, deadline, rng, best[0], consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
