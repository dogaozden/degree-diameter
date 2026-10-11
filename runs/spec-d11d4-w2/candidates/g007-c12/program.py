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
# Bi-Cayley (Haar-type) graphs over small groups, diameter 4.
# Base: two vertices joined by d darts, connection set S in a group G.
# ----------------------------------------------------------------------------

def _group_options(N):
    """Return (m, k, r) choices giving groups of order N: cyclic Z_N and Z_m x|_r Z_k."""
    opts = [(N, 1, 1)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _mul_table(m, k, r):
    """Full multiplication table of Z_m x|_r Z_k with element (a, b) coded as a*k+b (identity is 0)."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(m * k, dtype=np.int64)
    a = (x // k)[:, None]
    b = (x % k)[:, None]
    c = (x // k)[None, :]
    dd = (x % k)[None, :]
    na = (a + pw[b] * c) % m
    nb = (b + dd) % k
    return na * k + nb


def _sa_search(N, MT, inv, d, M3, deadline, rng):
    """Simulated annealing over connection sets S; return (True, S) on full coverage, else (False, best S)."""

    def cost(S):
        Q = MT[S[:, None], inv[S][None, :]]
        W = MT[Q[:, :, None], S[None, None, :]]
        cov = np.zeros(N, dtype=bool)
        cov[W[M3]] = True
        cov[S] = True
        return N - int(cov.sum())

    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = cost(S)
    best = cur
    bestS = S.copy()
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 1.5 * (1.0 - frac) + 0.1
        p = rng.randrange(d)
        inS = set(S.tolist())
        new = rng.randrange(N)
        while new in inS:
            new = rng.randrange(N)
        S2 = S.copy()
        S2[p] = new
        c2 = cost(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S = S2
            cur = c2
            if cur < best:
                best = cur
                bestS = S.copy()
    return cur == 0, bestS


def _find_connection_set(N, d, deadline, rng):
    """Try random groups of order N with SA on S until deadline; return (m, k, r, S) or None."""
    if N < d + 1:
        return None
    opts = _group_options(N)
    M3 = (~np.eye(d, dtype=bool))[:, :, None] & (~np.eye(d, dtype=bool))[None, :, :]
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        sub_deadline = min(deadline, time.monotonic() + 0.7)
        ok, S = _sa_search(N, MT, inv, d, M3, sub_deadline, rng)
        if ok:
            return (m, k, r, [int(s) for s in S])
    return None


def _bicayley(d, D, deadline, rng):
    """Bisection over group order N for the largest bi-Cayley graph of diameter <= D; return (n, edges) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    lo, hi = max(d + 1, 2), moore // 2
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        slot_end = min(deadline, time.monotonic() + 2.5)
        res = _find_connection_set(N, d, slot_end, rng)
        if res is not None:
            best = (N, res)
            lo = N + 1
        else:
            hi = N - 1
    if best is None:
        return None
    N, (m, k, r, S) = best
    order, mul, _ = lib.semidirect_group(m, k, r)
    darts = [(0, 1, g) for g in S]
    return lib.group_lift(2, darts, order, mul)


# ----------------------------------------------------------------------------
# NEW BOLD CONSTRUCTION: 4-vertex base lift over a group, diameter 4.
#
# Base graph K_{2,2} with multi-darts:
#   a1-b1: S0 (size s), a1-b2: S1 (size d-s), a2-b1: S2 (size d-s), a2-b2: S3 (size s).
# Lift has 4N vertices and degree d. Left multiplication by a group element is
# an automorphism, so distances from every vertex are determined by BFS from
# the four base representatives (u, e). This makes each check cheap (numpy BFS).
# Connection sets are searched by simulated annealing on the number of
# unreached (source, vertex) pairs at depth <= 4. Every result is re-verified
# with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _quad_adj(d, N, MT, inv, arr):
    """Adjacency array (4N x d) of the 4-base lift. Vertex (u, x) has id u*N + x; arr = 4 int64 sets."""
    s = len(arr[0])
    dw = d
    adj = np.zeros((4 * N, dw), dtype=np.int64)
    darts = [(0, 2, arr[0]), (0, 3, arr[1]), (1, 2, arr[2]), (1, 3, arr[3])]
    for u in (0, 1):
        blocks = [b * N + MT[:, S] for a, b, S in darts if a == u]
        adj[u * N:(u + 1) * N] = np.hstack(blocks)
    for v in (2, 3):
        blocks = [a * N + MT[:, inv[S]] for a, b, S in darts if b == v]
        adj[v * N:(v + 1) * N] = np.hstack(blocks)
    return adj


def _quad_cost(adj, N):
    """Total number of (source, vertex) pairs at distance > 4 from the four base representatives."""
    n = adj.shape[0]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        reach = np.zeros(n, dtype=bool)
        reach[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(4):
            nb = adj[front].ravel()
            nb = np.unique(nb[~reach[nb]])
            if nb.size == 0:
                break
            reach[nb] = True
            front = nb
        total += n - int(reach.sum())
    return total


def _quad_search(d, N, deadline, rng):
    """Search group and connection sets of order N; return (m, k, r, sets) with zero cost, or None."""
    s = d // 2
    sizes = [s, d - s, d - s, s]
    opts = _group_options(N)
    steps = 1500
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        arr = [np.array(rng.sample(range(N), sz), dtype=np.int64) for sz in sizes]
        adj = _quad_adj(d, N, MT, inv, arr)
        cur = _quad_cost(adj, N)
        for step in range(steps):
            if cur == 0:
                return (m, k, r, [a.tolist() for a in arr])
            if step % 128 == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(4)
            p = rng.randrange(sizes[i])
            old = int(arr[i][p])
            new = rng.randrange(N)
            while np.any(arr[i] == new):
                new = rng.randrange(N)
            arr[i][p] = new
            adj2 = _quad_adj(d, N, MT, inv, arr)
            c2 = _quad_cost(adj2, N)
            T = 1.0 * (1.0 - step / steps) + 0.05
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
                adj = adj2
            else:
                arr[i][p] = old
        if cur == 0:
            return (m, k, r, [a.tolist() for a in arr])
    return None


def _quad_lift(d, deadline, rng):
    """Bisection over N (group order) for the largest 4-base lift of diameter 4; return (n, edges) or None."""
    if d < 4:
        return None
    moore = lib._moore_bound(d, 4)
    lo = max(d + 1, moore // 8)
    hi = moore // 4
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        slot_end = min(deadline, time.monotonic() + 1.5)
        res = _quad_search(d, N, slot_end, rng)
        if res is not None:
            best = (N, res)
            lo = N + 1
        else:
            hi = N - 1
    if best is None:
        return None
    N, (m, k, r, sets) in [best]  # placeholder replaced below
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
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

    # Proven-strong path: bi-Cayley graphs over small groups (2-vertex base).
    if D >= 4:
        try:
            res = _bicayley(d, D, t0 + 0.45 * budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Bold path: 4-vertex base lifts over groups, searched with numpy BFS.
    if D == 4:
        try:
            res = _quad_lift(d, t0 + 0.85 * budget, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Twin construction on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
