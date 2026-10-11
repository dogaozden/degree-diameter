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
# NEW: Cayley-type bipartite lifts over small groups, found by local search.
#
# Group G of order N (semidirect Z_m x| Z_k, elements coded a*k+b, identity 0),
# connection set S of d distinct elements. Vertices a_x and b_x (x in G);
# a_x ~ b_{x*s} for s in S. Left multiplication is an automorphism, so it is
# enough to check distances from a_e (for a-a and a-b pairs) and from b_e
# (for b-b pairs). Order is 2N, degree d. A local search over S minimises the
# number of pairs at distance > 4.
# ----------------------------------------------------------------------------

def _groups(N):
    """Candidate (m, k, r) for groups of order N = m*k: abelian (r=1) and up to two non-abelian r per (m,k)."""
    out = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        out.append((m, k, 1))
        if k > 1:
            cnt = 0
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((m, k, r))
                    cnt += 1
                    if cnt >= 2:
                        break
    return out


def _table(N, m, k, r):
    """Multiplication table M[x, y] = x*y and inverse array for Z_m x|_r Z_k (vectorised)."""
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    M = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    rows, cols = np.nonzero(M == 0)
    inv = np.zeros(N, dtype=np.int64)
    inv[rows] = cols
    return M, inv


def _uncovered(M, S, Sinv, N, src):
    """Count pairs left uncovered within distance 4 from source vertex e on side src (0 = A, 1 = B).

    For src 0 this counts both sides (a-a and a-b pairs); for src 1 only the B side (b-b pairs).
    """
    visA = np.zeros(N, dtype=bool)
    visB = np.zeros(N, dtype=bool)
    front = np.array([0], dtype=np.int64)
    if src == 0:
        visA[0] = True
        side = 0
    else:
        visB[0] = True
        side = 1
    for _ in range(4):
        if side == 0:
            nb = np.unique(M[front[:, None], S[None, :]])
            nb = nb[~visB[nb]]
            visB[nb] = True
        else:
            nb = np.unique(M[front[:, None], Sinv[None, :]])
            nb = nb[~visA[nb]]
            visA[nb] = True
        front = nb
        side ^= 1
        if front.size == 0:
            break
    if src == 0:
        return int((N - visA.sum()) + (N - visB.sum()))
    return int(N - visB.sum())


def _cost(M, S, Sinv, N):
    return _uncovered(M, S, Sinv, N, 0) + _uncovered(M, S, Sinv, N, 1)


def _climb(M, inv, N, d, deadline, rng):
    """Local search over connection sets S of size d; return (best_S, best_cost)."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = _cost(M, S, inv[S], N)
    best = (cur, S.copy())
    stuck = 0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        T = S.copy()
        T[i] = c
        nc = _cost(M, T, inv[T], N)
        if nc <= cur or rng.random() < 0.02:
            S, cur = T, nc
        if cur < best[0]:
            best = (cur, S.copy())
            stuck = 0
        else:
            stuck += 1
        if stuck > 3000:
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            cur = _cost(M, S, inv[S], N)
            stuck = 0
    return best


def _cayley_edges(N, M, S):
    """Edges of the bipartite Cayley-type graph: a_x (vertex x) ~ b_{x*s} (vertex N + x*s)."""
    edges = []
    for x in range(N):
        for s in S:
            edges.append((x, N + int(M[x, s])))
    return 2 * N, edges


def _cayley_search(d, deadline, rng):
    """Search Cayley-type lifts of order near 0.8 * (Moore bound per side); return best (n, edges) or None."""
    M_bound = sum((d - 1) ** i for i in range(4))
    N_lo = max(d + 1, int(0.8 * M_bound))
    best = None
    deltas = (0, 1, 2, 4, 8, 12)
    for idx, delta in enumerate(deltas):
        now = time.monotonic()
        if now >= deadline:
            break
        N = N_lo + delta
        slice_end = now + (deadline - now) / (len(deltas) - idx)
        groups = _groups(N)
        if not groups:
            continue
        rng.shuffle(groups)
        groups = groups[:3]
        for gi, g in enumerate(groups):
            now = time.monotonic()
            if now >= slice_end:
                break
            g_end = now + (slice_end - now) / (len(groups) - gi)
            M, inv = _table(N, *g)
            cost, S = _climb(M, inv, N, d, g_end, rng)
            if cost == 0:
                n, edges = _cayley_edges(N, M, S)
                if best is None or n > best[0]:
                    best = (n, edges)
                break
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
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

    # NEW: Cayley-type bipartite lifts over small groups (diameter 4), local search.
    if D == 4 and d >= 3:
        try:
            cay_deadline = t0 + 0.3 * budget
            res = _cayley_search(d, cay_deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2) (degree d), then randomized set-cover extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.4 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < deadline - 1.0 and attempt < 4:
                remaining = deadline - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
