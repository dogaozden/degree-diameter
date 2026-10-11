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
# Greedy randomized set-cover vertex extension for diameter 4.
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
# NEW: bipartite Haar-type lifts over non-abelian groups Z_m x|_r Z_k.
#
# Graph H(G, S): side A and side B, each a copy of G; a_x ~ b_{x s} for s in S
# (|S| = d). Left multiplication by h is an automorphism on each side, so the
# diameter is <= 4 iff, from a_e and from b_e, the same-side vertices are all
# within 4 and the opposite-side vertices are all within 3. We search the
# d-subset S by simulated annealing on the number of uncovered targets, using
# a vectorised BFS over the group multiplication table. Any hit is validated
# with lib.is_valid before it is accepted, so this stage can only help.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Return (N, T, I): multiplication table and inverse array of Z_m x|_r Z_k (code a*k+b)."""
    N = m * k
    codes = np.arange(N, dtype=np.int64)
    A = codes // k
    B = codes % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    T = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    I = np.argmax(T == 0, axis=1)
    return N, T, I


def _pen(T, S, I, N):
    """Number of uncovered (start, target) pairs for the Haar graph with connection set S."""
    Sarr = np.array(S, dtype=np.int64)
    Sinv = I[Sarr]
    total = 0
    for start in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        seen[start][0] = True
        fr = np.array([0], dtype=np.int64)
        side = start
        for _ in range(4):
            cols = Sarr if side == 0 else Sinv
            nxt = T[np.ix_(fr, cols)].ravel()
            mark = np.zeros(N, dtype=bool)
            mark[nxt] = True
            mark &= ~seen[1 - side]
            seen[1 - side] |= mark
            fr = np.flatnonzero(mark)
            side = 1 - side
            if fr.size == 0:
                break
        total += int(N - seen[0].sum()) + int(N - seen[1].sum())
    return total


def _sa(T, I, N, d, end, rng):
    """Simulated annealing for a zero-penalty connection set S of size d; returns S or None."""
    S = rng.sample(range(N), d)
    inS = set(S)
    pen = _pen(T, S, I, N)
    start = time.monotonic()
    span = max(1e-3, end - start)
    while True:
        if pen == 0:
            return S
        now = time.monotonic()
        if now >= end:
            return None
        temp = max(0.08, 1.2 * (1.0 - (now - start) / span))
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in inS:
            continue
        S2 = list(S)
        old = S2[i]
        S2[i] = g
        p2 = _pen(T, S2, I, N)
        delta = p2 - pen
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            inS.discard(old)
            inS.add(g)
            S = S2
            pen = p2


def _haar_stage(d, lo, hi, deadline, rng):
    """Search Haar graphs over non-abelian groups of order in [lo, hi]; return (n, edges) or None."""
    cands = []
    for k in range(2, min(hi, 60) + 1):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append((m, k, r))
    if not cands:
        return None
    rng.shuffle(cands)
    best = None
    for (m, k, r) in cands:
        now = time.monotonic()
        if now > deadline - 0.5:
            break
        N_guess = m * k
        if best is not None and N_guess <= best[0]:
            continue
        N, T, I = _group_table(m, k, r)
        slice_end = min(deadline, now + 5.0)
        S = _sa(T, I, N, d, slice_end, rng)
        if S is not None:
            best = (N, S, T)
    if best is None:
        return None
    N, S, T = best

    def mulf(x, g):
        return int(T[x, g])

    return lib.group_lift(2, [(0, 1, int(s)) for s in S], N, mulf)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    parent_deadline = t0 + 0.5 * budget
    twin_deadline = t0 + 0.25 * budget
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

    # NEW stage for diameter 4: Haar-type lifts over non-abelian groups,
    # searching for graphs with more than the current best order.
    if D == 4 and d >= 3 and lib.is_valid(best[0], best[1], d, D):
        lo = best[0] // 2 + 1
        hi = sum((d - 1) ** i for i in range(4))  # Moore bound / 2 for bipartite, D = 4
        if lo <= hi:
            try:
                res = _haar_stage(d, lo, hi, deadline - 0.5, rng)
                if res is not None:
                    consider(*res)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
