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
# New construction: bi-Cayley graphs over finite non-abelian groups.
#
# Group G = Z_m x| Z_k with x=(a,b) coded as a*k+b, product (a,b)(c,d) = (a + r^b c, b + d).
# Vertices: A-side x in G (id x), B-side y in G (id N + y). Edge (A,x)-(B,x*s) for each
# s in S, |S| = d. This is d-regular and bipartite. Left multiplication by G is an
# automorphism, so the diameter is at most D iff both roots (A,e) and (B,e) reach
# all 2N vertices within D steps. A hill climb on S minimises the total number of
# unreached (root, vertex) pairs; each evaluation is a few vectorised BFS levels.
# ----------------------------------------------------------------------------

def _options(N, d):
    """Return (m, k, r) semidirect parameters of order N, cyclic option first for k = 1."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                opts.append((m, k, r))
    return opts


def _table(m, k, r):
    """Multiplication table T[x, y] = x*y for the semidirect group Z_m x| Z_k (identity is 0)."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    powr = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    T = ((a[:, None] + powr[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return T


def _cost(T, S, Sinv, N, D):
    """Total number of (root, vertex) pairs not reached within D steps, roots (A,e) and (B,e)."""
    total = 0
    for side0 in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        if side0 == 0:
            visA[0] = True
        else:
            visB[0] = True
        cur = np.array([0], dtype=np.int64)
        side = side0
        for _ in range(D):
            gens = S if side == 0 else Sinv
            tgt = visB if side == 0 else visA
            nb = T[cur[:, None], gens[None, :]].ravel()
            nb = nb[~tgt[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            tgt[nb] = True
            cur = nb
            side ^= 1
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _climb(T, inv, N, d, D, deadline, rng):
    """Hill-climb a generator set S of size d with zero cost; return S as an array or None."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cost = _cost(T, S, inv[S], N, D)
    stall = 0
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 4000:
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            cost = _cost(T, S, inv[S], N, D)
            stall = 0
            continue
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = _cost(T, S2, inv[S2], N, D)
        if c2 <= cost or rng.random() < 0.01:
            if c2 < cost:
                stall = 0
            S, cost = S2, c2
    return S


def _bicayley_edges(T, S, N):
    """Return (2N, edges) for the bi-Cayley graph with connection set S."""
    sub = T[:, S].tolist()
    edges = []
    for x in range(N):
        for y in sub[x]:
            edges.append((x, N + y))
    return 2 * N, edges


def _bicayley_search(d, D, N_lo, N_hi, deadline, rng, consider):
    """Try bi-Cayley graphs of order 2N for N = N_lo, N_lo+1, ... up to N_hi, within deadline."""
    N = N_lo
    while N <= N_hi and time.monotonic() < deadline and N >= d:
        now = time.monotonic()
        remaining = deadline - now
        opts = _options(N, d)
        if opts:
            nonab = [o for o in opts if o[1] > 1]
            pool = nonab or opts
            m, k, r = rng.choice(pool)
            T = _table(m, k, r)
            inv = np.argmax(T == 0, axis=1)
            slice_end = min(deadline, now + max(2.0, remaining / 5.0))
            S = _climb(T, inv, N, d, D, slice_end, rng)
            if S is not None:
                n, edges = _bicayley_edges(T, S, N)
                consider(n, edges)
        N += 1


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

    # Bold branch: bi-Cayley graphs over non-abelian groups, degree exactly d.
    if D >= 2 and d >= 3 and best[0] < moore:
        N_lo = best[0] // 2 + 1
        N_hi = moore // 2
        if N_lo <= N_hi:
            try:
                _bicayley_search(d, D, N_lo, N_hi, deadline, rng, consider)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
