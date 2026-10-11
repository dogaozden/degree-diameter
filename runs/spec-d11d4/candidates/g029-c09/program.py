import itertools
import random
import time
from math import gcd

import numpy as np

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
# Generalized voltage lifts over (possibly non-abelian) groups Z_m x|_r Z_k.
#
# Base: kb vertices on side A (0..kb-1) and kb on side B (kb..2kb-1). The base
# has d darts per A vertex, dart i joining A-vertex u to B-vertex kb+perm[i][u]
# with voltage volt[i][u] in G. The lift has vertices (b, x), x in G, and the
# edge (u, x)-(v, x*g). Left translation by G is an automorphism, so the
# diameter is at most D iff every base vertex (b, identity) reaches the whole
# lift within D steps. The defect is the number of unreached (source, vertex)
# pairs, evaluated for all sources at once with numpy boolean arrays.
# ----------------------------------------------------------------------------

def _group_options(M):
    """All (m, k, r) with m*k = M giving a semidirect product Z_m x|_r Z_k (r = 1 is the direct product)."""
    opts = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        opts.append((m, k, 1))
        if m > 1 and k > 1:
            for r in range(2, m):
                if gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    opts.append((m, k, r))
    return opts


def _group_tables(m, k, r):
    """Vectorised multiplication table (as mtT, with mtT[g, x] = x*g) and inverse array for the group."""
    M = m * k
    r %= m
    X = np.arange(M, dtype=np.int64)
    a, b = X // k, X % k
    powers = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64) % m
    c, dd = X // k, X % k
    A = (a[:, None] + powers[b][:, None] * c[None, :]) % m
    Bv = (b[:, None] + dd[None, :]) % k
    mt = A * k + Bv  # mt[x, y] = x*y
    nb = (-b) % k
    iv = ((-powers[nb] * a) % m) * k + nb
    mtT = np.ascontiguousarray(mt.T)
    return mtT, iv.astype(np.int64)


def _lift_defect(kb, D, perm, volt, mtT, iv):
    """Number of unreached (source, vertex) pairs within D steps; 0 means the lift has diameter <= D."""
    M = mtT.shape[0]
    B2 = 2 * kb
    R = np.zeros((B2, B2, M), dtype=bool)
    for s in range(B2):
        R[s, s, 0] = True
    darts = []
    for i in range(len(perm)):
        pi, vi = perm[i], volt[i]
        for u in range(kb):
            v = kb + pi[u]
            g = vi[u]
            darts.append((u, v, mtT[g], mtT[iv[g]]))
    for _ in range(D):
        N = R.copy()
        for u, v, f, bk in darts:
            N[:, v, f] |= R[:, u, :]
            N[:, u, bk] |= R[:, v, :]
        R = N
        if R.all():
            break
    return int(B2 * B2 * M - np.count_nonzero(R))


def _lift_graph(kb, perm, volt, mtT):
    """Return (n, edges) for the lift described by perm and volt."""
    M = mtT.shape[0]
    E = set()
    for i in range(len(perm)):
        for u in range(kb):
            v = kb + perm[i][u]
            g = volt[i][u]
            f = mtT[g].tolist()
            for x in range(M):
                a = u * M + x
                b = v * M + f[x]
                E.add((a, b) if a < b else (b, a))
    return 2 * kb * M, sorted(E)


def _lift_search(d, D, kb, mtT, iv, deadline, rng):
    """Hill-climb voltages and matchings for a zero-defect lift; return (perm, volt) or None."""
    M = mtT.shape[0]
    STALL = 300

    def fresh():
        perm = [rng.sample(range(kb), kb) for _ in range(d)]
        volt = [[rng.randrange(M) for _ in range(kb)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _lift_defect(kb, D, perm, volt, mtT, iv)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > STALL:
            perm, volt = fresh()
            cur = _lift_defect(kb, D, perm, volt, mtT, iv)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(kb)
        if rng.random() < 0.7:
            old = volt[i][u]
            volt[i][u] = rng.randrange(M)
            new = _lift_defect(kb, D, perm, volt, mtT, iv)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(kb)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _lift_defect(kb, D, perm, volt, mtT, iv)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return perm, volt


def _group_phase(d, D, bn, moore, deadline, rng, consider):
    """Repeatedly search non-abelian and cyclic voltage lifts of order above bn until deadline or Moore bound."""
    while time.monotonic() < deadline and bn < moore:
        ks = [kb for kb in (2, 3, 4, 5, 6) if 2 * kb * (bn // (2 * kb) + 1) <= moore]
        if not ks:
            break
        kb = rng.choice(ks)
        M = bn // (2 * kb) + 1 + rng.randrange(0, 3)
        if 2 * kb * M > moore:
            M = bn // (2 * kb) + 1
        opts = _group_options(M)
        nonab = [o for o in opts if o[1] > 1 and o[2] != 1]
        if nonab and rng.random() < 0.6:
            m, k, r = rng.choice(nonab)
        else:
            m, k, r = rng.choice(opts)
        mtT, iv = _group_tables(m, k, r)
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, (deadline - now) / 3.0))
        res = _lift_search(d, D, kb, mtT, iv, slice_end, rng)
        if res is not None:
            perm, volt = res
            n, edges = _lift_graph(kb, perm, volt, mtT)
            if n > bn and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                bn = n
    return bn


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.5 * budget
    twin_deadline = t0 + 0.35 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1) and best[0] < moore:
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 and best[0] < moore:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11 and best[0] < moore:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Generalized voltage lifts over cyclic and semidirect groups.
    if D >= 2 and d >= 2 and best[0] < moore:
        try:
            _group_phase(d, D, best[0], moore, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
