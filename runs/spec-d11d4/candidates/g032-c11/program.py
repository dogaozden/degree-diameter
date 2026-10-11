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
# NEW: bi-Cayley (Haar-type) graphs over small groups, found by local search.
#
# Group G of order N, connection set S of size d. Vertices a_g = g and
# b_g = N + g; edge a_g -- b_{g*s} for s in S. Every such graph is bipartite,
# d-regular, and both sides are vertex-transitive under left multiplication.
# So diameter <= 4 holds iff, from a_e and from b_e, every vertex of the
# matching side is reached within 4 steps. Those reach sets are computed
# with set products, and the local search minimizes the number of misses.
# Groups are semidirect products Z_m x| Z_k (k = 1 gives cyclic groups).
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a, b) coded as a*k+b; identity is 0."""
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    g = np.arange(m * k, dtype=np.int64)
    A = g // k
    B = g % k
    Ax, Bx = A[:, None], B[:, None]
    Ay, By = A[None, :], B[None, :]
    M = ((Ax + P[Bx] * Ay) % m) * k + (Bx + By) % k
    nb = (-B) % k
    inv = ((-P[nb] * A) % m) * k + nb
    return M, inv


def _group_tables(N, rng):
    """Return a shuffled list of (mul_table, inv_table) for several groups of order N."""
    tabs = []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            rs = [1]
        else:
            rs = {1}
            if m > 2:
                for _ in range(60):
                    r = rng.randrange(2, m)
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                        rs.add(r)
                    if len(rs) >= 4:
                        break
            rs = list(rs)
        for r in rs:
            tabs.append(_table(m, k, r))
    rng.shuffle(tabs)
    return tabs[:8]


def _uncovered(M, inv, S):
    """Number of vertices not within distance 4 of a_e or b_e (0 means diameter <= 4)."""
    N = M.shape[0]
    Si = inv[S]
    SS = M[S[:, None], Si[None, :]]                       # s t^-1
    D2 = np.unique(SS)
    E = np.zeros(N, dtype=bool)                           # a-side, even distance from a_e
    E[0] = True
    E[D2] = True
    E[np.unique(M[D2[:, None], D2[None, :]])] = True
    O = np.zeros(N, dtype=bool)                           # b-side, odd distance from a_e
    O[S] = True
    O[np.unique(M[SS.ravel()[:, None], S[None, :]])] = True
    T = np.unique(M[Si[:, None], S[None, :]])             # t^-1 s
    Ep = np.zeros(N, dtype=bool)                          # b-side, even distance from b_e
    Ep[0] = True
    Ep[T] = True
    Ep[np.unique(M[T[:, None], T[None, :]])] = True
    Op = np.zeros(N, dtype=bool)                          # a-side, odd distance from b_e
    Op[Si] = True
    Op[np.unique(M[T[:, None], Si[None, :]])] = True
    covered = int(E.sum()) + int(O.sum()) + int(Ep.sum()) + int(Op.sum())
    return 4 * N - covered


def _search(M, inv, d, t_end, rng):
    """Simulated annealing over connection sets S; return S with zero cost, or None before t_end."""
    N = M.shape[0]
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cost = _uncovered(M, inv, S)
    while cost > 0 and time.monotonic() < t_end:
        i = rng.randrange(d)
        v = rng.randrange(N)
        if np.any(S == v):
            continue
        S2 = S.copy()
        S2[i] = v
        c2 = _uncovered(M, inv, S2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / 0.7):
            S, cost = S2, c2
    return S if cost == 0 else None


def _edges(M, S, N):
    """Edge list of the bi-Cayley graph: a_g -- b_{g s} with b_h = N + h."""
    tgt = M[np.arange(N)[:, None], S[None, :]]
    src = np.repeat(np.arange(N), len(S))
    dst = N + tgt.ravel()
    return list(zip(src.tolist(), dst.tolist()))


def _haar_search(d, start, t_end, rng, consider):
    """Try orders N = start, start+1, ... ; each success is offered to consider(2N, edges)."""
    N = start
    while time.monotonic() < t_end:
        now = time.monotonic()
        slice_end = min(t_end, now + max(2.0, 0.5 * (t_end - now)))
        groups = _group_tables(N, rng)
        if not groups:
            return
        found = None
        chosen = None
        while found is None and time.monotonic() < slice_end:
            for M, inv in groups:
                if time.monotonic() >= slice_end:
                    break
                found = _search(M, inv, d, min(slice_end, time.monotonic() + 1.5), rng)
                if found is not None:
                    chosen = (M, found)
                    break
        if chosen is None:
            return
        M, S = chosen
        consider(2 * N, _edges(M, S, N))
        N += 1


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

    # NEW: bi-Cayley search for diameter 4, using a short slice of the budget.
    if D == 4 and d >= 3:
        try:
            mb = 2 * sum((d - 1) ** i for i in range(4))   # Moore bound for D = 4
            start = max(2, int(0.8 * mb / 2))
            haar_end = t0 + 0.25 * budget
            _haar_search(d, start, haar_end, rng, consider)
        except Exception:
            pass

    now = time.monotonic()

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = now + 0.5 * max(0.0, deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
