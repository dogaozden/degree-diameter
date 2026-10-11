import itertools
import math
import random
import time

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
    c = [0] * n          # number of neighbours of v inside S
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
            # Restart from the best independent set found so far.
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
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
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
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# existing vertex. Adding x only shortens distances, so no other pair can break.
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
# Bold alternative for diameter 4: bi-Cayley graphs over small non-abelian groups.
#
# Two sides, copies of a finite group G of order N. Vertex (x,0) is joined to
# (x*g,1) for every g in S, |S| = d. The graph is d-regular, bipartite, and
# vertex-transitive on each side, so diameter <= 4 reduces to two covering
# conditions around the identity:
#   odd distances (<= 3):  S S^-1 S   covers G
#   even distances (<= 4): (S S^-1)(S S^-1) covers G
# Local search (simulated annealing) over S minimises the number of uncovered
# group elements. Groups are semidirect products Z_m x| Z_k (and cyclic).
# ----------------------------------------------------------------------------

def _groups_of_order(N, rng, cap=10):
    """Return a shuffled sample of (m, k, r) with N = m*k encoding Z_m x|_r Z_k."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(0, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    rng.shuffle(opts)
    return opts[:cap]


def _table(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a,b) coded a*k+b (matches lib.semidirect_group)."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    A = x // k
    B = x % k
    powr = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    pb = powr[B]
    M = ((A[:, None] + pb[:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    nb = (-B) % k
    inv = ((-powr[nb] * A) % m) * k + nb
    return M, inv


def _search(d, N, M, inv, end, rng):
    """Simulated annealing for a d-subset S of G whose two covering conditions hold; return S or None."""

    def misses(S):
        Sa = np.array(S, dtype=np.int64)
        Dset = np.unique(M[Sa[:, None], inv[Sa][None, :]])
        c1 = np.zeros(N, dtype=bool)
        c1[M[Dset[:, None], Sa[None, :]].ravel()] = True
        c2 = np.zeros(N, dtype=bool)
        c2[M[Dset[:, None], Dset[None, :]].ravel()] = True
        return 2 * N - int(c1.sum()) - int(c2.sum())

    while time.monotonic() < end:
        S = rng.sample(range(N), d)
        cur = misses(S)
        T = 2.0
        for _ in range(20000):
            if cur == 0:
                return S
            if time.monotonic() >= end:
                return None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            S2 = list(S)
            S2[i] = x
            c = misses(S2)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S, cur = S2, c
            T = max(0.3, T * 0.9997)
    return None


def _bold_bicayley(d, D, best_n, deadline, rng):
    """Try to find a bi-Cayley graph with 2N vertices, N >= best_n/2 + 1; return (n, edges) or None."""
    if D < 4 or d < 3:
        return None
    N0 = best_n // 2 + 1
    cands = [N0, N0 + 1, N0 + 2]
    while time.monotonic() < deadline and cands:
        N = rng.choice(cands)
        if N > 3000:
            cands.remove(N)
            continue
        opts = _groups_of_order(N, rng)
        if not opts:
            cands.remove(N)
            continue
        m, k, r = rng.choice(opts)
        M, inv = _table(m, k, r)
        slice_end = min(deadline, time.monotonic() + 4.0)
        S = _search(d, N, M, inv, slice_end, rng)
        if S is None:
            continue
        edges = []
        for g in S:
            col = M[:, g].tolist()
            edges.extend((x, N + c) for x, c in enumerate(col))
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    # Parent path (twin graph + extension) gets the first half of the budget
    # when D >= 4; the bold bi-Cayley search gets whatever remains.
    parent_deadline = t0 + (0.5 * budget if D >= 4 else budget)
    twin_deadline = t0 + (0.25 * budget if D >= 4 else 0.5 * budget)

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold change: bi-Cayley graphs over semidirect products, aiming to beat the best so far.
    if D >= 4 and d >= 3:
        try:
            res = _bold_bicayley(d, D, best[0], t0 + budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
