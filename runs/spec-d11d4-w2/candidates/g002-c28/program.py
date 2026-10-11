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
# NEW BOLD CONSTRUCTION: two-base-vertex-per-side group lifts (t = 2).
#
# Base graph: sides A = {0, 1}, B = {2, 3}. Each pair (i, j) carries a set S_ij
# of darts in a group G of order N, with |S00| = |S11| = a and |S01| = |S10| = b,
# a + b = d. Every base vertex then has degree d and the lift has 4N vertices.
#
# Left translation is an automorphism of the lift, so the diameter is determined
# by four balls: radius-4 balls around (block u, identity) for u = 0..3. Those
# coverage counts give an exact cost, which simulated annealing drives to zero.
# Each candidate is still verified with lib.is_valid before use.
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


def _build_nb(darts, N, nblocks, d, MT, inv):
    """Neighbour array (n, d) of the lift; dart (u, v, g) joins (u, x) to (v, x*g)."""
    n = nblocks * N
    nb = np.empty((n, d), dtype=np.int64)
    ptr = [0] * nblocks
    ar = np.arange(N, dtype=np.int64)
    for u, v, g in darts:
        nb[u * N + ar, ptr[u]] = v * N + MT[ar, g]
        nb[v * N + ar, ptr[v]] = u * N + MT[ar, inv[g]]
        ptr[u] += 1
        ptr[v] += 1
    return nb


def _cover_cost(nb, n, N, nblocks, D=4):
    """Total number of vertices NOT within distance D of the identity of each block (0 means diameter <= D)."""
    total = 0
    for b in range(nblocks):
        src = b * N
        reach = np.zeros(n, dtype=bool)
        reach[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = np.zeros(n, dtype=bool)
            cand[nb[frontier].ravel()] = True
            cand &= ~reach
            if not cand.any():
                break
            reach |= cand
            frontier = np.nonzero(cand)[0]
        total += n - int(reach.sum())
    return total


def _multi_search(d, N, deadline, rng):
    """Simulated annealing over the t=2 dart sets in a group of order N; return (m, k, r, darts) or None."""
    a = d // 2
    b = d - a
    if a < 1 or b < 1 or N < d:
        return None
    opts = _group_options(N)
    m, k, r = rng.choice(opts)
    MT = _mul_table(m, k, r)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    keys = [(0, 0), (0, 1), (1, 0), (1, 1)]
    size = {(0, 0): a, (0, 1): b, (1, 0): b, (1, 1): a}
    sets = {kk: rng.sample(range(N), size[kk]) for kk in keys}

    def darts_of(st):
        return [(kk[0], 2 + kk[1], g) for kk in keys for g in st[kk]]

    def cost_of(st):
        nb = _build_nb(darts_of(st), N, 4, d, MT, inv)
        return _cover_cost(nb, 4 * N, N, 4)

    cur = cost_of(sets)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 2.0 * (1.0 - frac) + 0.05
        kk = rng.choice(keys)
        pos = rng.randrange(len(sets[kk]))
        inset = set(sets[kk])
        new = rng.randrange(N)
        while new in inset:
            new = rng.randrange(N)
        old = sets[kk][pos]
        sets[kk][pos] = new
        c2 = cost_of(sets)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            sets[kk][pos] = old
    if cur == 0:
        return (m, k, r, darts_of(sets))
    return None


def _multi_base(d, D, deadline, rng):
    """Bisection over group order N for the largest t=2 lift of diameter <= D; return (n, edges) or None."""
    if D != 4 or d < 3:
        return None
    moore = lib._moore_bound(d, D)
    hi = moore // 4
    lo = max(d + 1, (3 * hi) // 4)
    best = None
    while lo <= hi and time.monotonic() < deadline:
        N = (lo + hi + 1) // 2
        slot_end = min(deadline, time.monotonic() + 2.5)
        res = None
        while time.monotonic() < slot_end and res is None:
            res = _multi_search(d, N, min(slot_end, time.monotonic() + 0.8), rng)
        if res is not None:
            best = (N, res)
            lo = N + 1
        else:
            hi = N - 1
    if best is None:
        return None
    N, (m, k, r, darts) = best
    order, mul = lib.semidirect_group(m, k, r)
    return lib.group_lift(4, darts, order, mul)


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

    # Twin construction on W(d-2) using the spare degree slot (degree d, diameter 4).
    twin_deadline = t0 + 0.6 * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, twin_deadline, rng))
        except Exception:
            pass

    # New bold path: two-base-vertex-per-side group lifts with searched dart sets.
    if D >= 4:
        try:
            res = _multi_base(d, D, deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
