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
# Group helpers shared by the lift searches.
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


# ----------------------------------------------------------------------------
# NEW BOLD CONSTRUCTION: 2x2-base group lifts (a 4-vertex base graph).
#
# Base graph: A0, A1 on one side, B0, B1 on the other. Block (i, j) carries a
# set S_ij of group elements (distinct within a block). Vertex (i, x) in A_i
# is adjacent to (j, x*s) in B_j for s in S_ij. Block sizes are
#   S00 = x, S01 = d-x, S10 = d-x, S11 = x,  so every vertex has degree d.
#
# Left translation is an automorphism, so diameter <= 4 is equivalent to the
# eccentricity of the four identity vertices being <= 4. The cost of a
# candidate is the number of vertices not reached from those four sources
# within 4 steps; simulated annealing drives it to zero. The group order N
# is raised one step at a time, and every success is validated with lib.is_valid.
# ----------------------------------------------------------------------------

def _build_nbr(N, MT, inv, blocks, d):
    """Neighbour array (4N, d): A-side rows 0..2N-1, B-side rows 2N..4N-1."""
    V = 4 * N
    nbr = np.empty((V, d), dtype=np.int64)
    xs = np.arange(N, dtype=np.int64)
    for i in range(2):
        cols = [2 * N + j * N + MT[xs[:, None], blocks[i][j][None, :]] for j in range(2)]
        nbr[i * N:(i + 1) * N] = np.hstack(cols)
    for j in range(2):
        cols = [i * N + MT[xs[:, None], inv[blocks[i][j]][None, :]] for i in range(2)]
        nbr[2 * N + j * N:2 * N + (j + 1) * N] = np.hstack(cols)
    return nbr


def _uncovered(nbr, srcs, V, D):
    """Total number of vertices not within distance D of each source (vectorised BFS)."""
    unc = 0
    for s in srcs:
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        front = seen.copy()
        for _ in range(D):
            reach = np.zeros(V, dtype=bool)
            reach[nbr[front].ravel()] = True
            front = reach & ~seen
            seen |= front
        unc += V - int(seen.sum())
    return unc


def _sa2(N, MT, inv, d, x, deadline, rng):
    """Simulated annealing over the four block sets; return (True, blocks) on full coverage."""
    sizes = [[x, d - x], [d - x, x]]
    V = 4 * N
    srcs = [0, N, 2 * N, 3 * N]

    def cost(bl):
        return _uncovered(_build_nbr(N, MT, inv, bl, d), srcs, V, 4)

    blocks = [[np.array(rng.sample(range(N), sizes[i][j]), dtype=np.int64)
               for j in range(2)] for i in range(2)]
    cur = cost(blocks)
    best = cur
    bestb = [[b.copy() for b in row] for row in blocks]
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 2.0 * (1.0 - frac) + 0.2
        i, j = rng.randrange(2), rng.randrange(2)
        p = rng.randrange(sizes[i][j])
        present = set(blocks[i][j].tolist())
        new = rng.randrange(N)
        while new in present:
            new = rng.randrange(N)
        nb = [[b.copy() for b in row] for row in blocks]
        nb[i][j][p] = new
        c2 = cost(nb)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            blocks = nb
            cur = c2
            if cur < best:
                best = cur
                bestb = [[b.copy() for b in row] for row in blocks]
    return cur == 0, bestb


def _lift2_find(N, d, deadline, rng):
    """Try random groups of order N and random block sizes until deadline; return (MT, blocks) or None."""
    opts = _group_options(N)
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        x = rng.randint(1, d - 1)
        sub = min(deadline, time.monotonic() + 4.0)
        ok, blocks = _sa2(N, MT, inv, d, x, sub, rng)
        if ok:
            return MT, blocks
    return None


def _edges_from_blocks(N, MT, inv, blocks, d):
    nbr = _build_nbr(N, MT, inv, blocks, d)
    return [(a, int(b)) for a in range(2 * N) for b in nbr[a].tolist()]


def _lift2_search(d, D, deadline, rng, target_n):
    """Find 2x2-base lifts with more than target_n vertices; return the largest valid (n, edges) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    N = target_n // 4 + 1
    best = None
    while time.monotonic() < deadline and 4 * N <= moore:
        found = _lift2_find(N, d, deadline, rng)
        if found is None:
            break
        MT, blocks = found
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        edges = _edges_from_blocks(N, MT, inv, blocks, d)
        if lib.is_valid(4 * N, edges, d, D):
            best = (4 * N, edges)
            N += 1
        else:
            break
    return best


# ----------------------------------------------------------------------------
# Older bi-Cayley path (one-vertex-per-side base, Haar type), kept as a fallback.
# ----------------------------------------------------------------------------

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
    """Bisection over group order N for the largest Haar-type lift of diameter <= D; return (n, edges) or None."""
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
    order, mul = lib.semidirect_group(m, k, r)
    darts = [(0, 1, g) for g in S]
    return lib.group_lift(2, darts, order, mul)


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

    # Bold path: 2x2-base group lifts, aiming for more than the current best order.
    if D >= 4 and d >= 3:
        try:
            res = _lift2_search(d, D, t0 + 0.50 * budget, rng, best[0])
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Haar-type bi-Cayley lifts (previous main path), limited share of the budget.
    if D >= 4:
        try:
            res = _bicayley(d, D, min(deadline, time.monotonic() + 0.20 * budget), rng)
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
