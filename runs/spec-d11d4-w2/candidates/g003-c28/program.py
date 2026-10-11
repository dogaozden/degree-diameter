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
# Group helpers (cyclic and semidirect Z_m x| Z_k).
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
# NEW CONSTRUCTION: two-orbit bi-Cayley lifts (four base vertices, 2 per side).
#
# Base: A_0, A_1 (left side) and B_0, B_1 (right side). The block of darts
# from A_i to B_j carries c_ij group voltages, with c = [[a, b], [b, a]],
# a = ceil(d/2), b = floor(d/2), so every base vertex has degree d.
# Lift over a group G of order N: A_{i,x} ~ B_{j, x*g} for each dart (i, j, g).
# Order 4N, bipartite, d-regular.
#
# Left multiplication is an automorphism that fixes each side, so the ball
# of every vertex is a translate of the ball of one of the four base-identity
# vertices (A_0,e), (A_1,e), (B_0,e), (B_1,e). Diameter <= D therefore holds
# iff those four sources reach everything within D steps.
# Coverage is checked for all four sources at once with boolean numpy
# propagation over the lifted neighbour array, and simulated annealing moves
# one voltage at a time. The group order N is found by bisection.
# ----------------------------------------------------------------------------

def _block_sizes(d):
    a = (d + 1) // 2
    b = d // 2
    return [(0, 0, a), (0, 1, b), (1, 0, b), (1, 1, a)]


def _dart_layout(d):
    I, J, B = [], [], []
    for bi, (i, j, c) in enumerate(_block_sizes(d)):
        I += [i] * c
        J += [j] * c
        B += [bi] * c
    return np.array(I, np.int64), np.array(J, np.int64), np.array(B, np.int64)


def _lift_nbr(N, MT, inv, I, J, G, d):
    """Neighbour array of the lift: row v lists the d neighbours of vertex v (A rows first, then B rows)."""
    xs = np.arange(N, dtype=np.int64)[:, None]
    parts = []
    for i in (0, 1):
        T = np.nonzero(I == i)[0]
        parts.append(2 * N + J[T][None, :] * N + MT[xs, G[T][None, :]])
    for j in (0, 1):
        U = np.nonzero(J == j)[0]
        parts.append(I[U][None, :] * N + MT[xs, inv[G[U]][None, :]])
    return np.vstack(parts)


def _uncovered(nbr, srcs, V, steps):
    """Number of (source, vertex) pairs not reached within `steps` steps from the sources."""
    R = np.zeros((len(srcs), V), dtype=bool)
    R[np.arange(len(srcs)), srcs] = True
    for _ in range(steps):
        new = R.copy()
        for k in range(nbr.shape[1]):
            new |= R[:, nbr[:, k]]
        R = new
    return int(R.size - np.count_nonzero(R))


def _sa_lift(N, d, D, MT, inv, deadline, rng):
    """Simulated annealing over voltages; return (True, G) on full coverage, else (False, G)."""
    I, J, blk = _dart_layout(d)
    E = len(blk)
    G = np.zeros(E, dtype=np.int64)
    for bi in range(4):
        idx = np.nonzero(blk == bi)[0]
        if len(idx):
            G[idx] = rng.sample(range(N), len(idx))
    V = 4 * N
    srcs = [0, N, 2 * N, 3 * N]

    def cost(g):
        return _uncovered(_lift_nbr(N, MT, inv, I, J, g, d), srcs, V, D)

    cur = cost(G)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 2.0 * (1.0 - frac) + 0.1
        t = rng.randrange(E)
        used = {int(G[s]) for s in range(E) if blk[s] == blk[t] and s != t}
        g = rng.randrange(N)
        while g in used:
            g = rng.randrange(N)
        G2 = G.copy()
        G2[t] = g
        c2 = cost(G2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            G, cur = G2, c2
    return cur == 0, G


def _find_lift(N, d, D, slot_end, rng):
    """Random groups of order N with SA on voltages until slot_end; return (G, MT, inv) or None."""
    opts = _group_options(N)
    while time.monotonic() < slot_end:
        m, k, r = rng.choice(opts)
        MT = _mul_table(m, k, r)
        inv = np.argmax(MT == 0, axis=1).astype(np.int64)
        sub = min(slot_end, time.monotonic() + 1.5)
        ok, G = _sa_lift(N, d, D, MT, inv, sub, rng)
        if ok:
            return G, MT, inv
    return None


def _lift_graph(N, d, MT, inv, G):
    """Build (4N, edges) from the voltage assignment."""
    I, J, _ = _dart_layout(d)
    nbr = _lift_nbr(N, MT, inv, I, J, G, d)
    edges = [(v, w) for v in range(2 * N) for w in nbr[v].tolist()]
    return 4 * N, edges


def _multi_search(d, D, lo, hi, deadline, rng, consider):
    """Bisection over group order N in [lo, hi] for feasible two-orbit lifts."""
    good, bad = lo - 1, hi + 1
    while good + 1 < bad and time.monotonic() < deadline:
        N = lo if good < lo else (good + bad) // 2
        remaining = deadline - time.monotonic()
        slot_end = min(deadline, time.monotonic() + max(2.0, remaining / 3.0))
        res = _find_lift(N, d, D, slot_end, rng)
        if res is None:
            bad = N
        else:
            G, MT, inv = res
            consider(*_lift_graph(N, d, MT, inv, G))
            good = N


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    # Calibration cases reaching the Moore bound return at once.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin construction on W(d-2) using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, t0 + 0.4 * budget, rng))
        except Exception:
            pass

    # New construction: two-orbit bi-Cayley lifts with 4 base vertices.
    if d >= 2 and D >= 2 and best[0] < lib.moore_bound(d, D):
        lo = best[0] // 4 + 1
        hi = lib.moore_bound(d, D) // 4
        try:
            _multi_search(d, D, lo, hi, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
