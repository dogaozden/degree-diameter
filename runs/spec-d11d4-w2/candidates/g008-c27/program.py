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
# Bi-Cayley voltage lifts over small groups, found by annealing.
#
# Group G of order N (given by its multiplication table). Vertices A_x and B_x
# for x in G. Choose a connection set S of d distinct group elements and join
# A_x to B_{x*s} for every s in S. This is d-regular and bipartite. Left
# multiplication is an automorphism, so diameter <= 4 is equivalent to every
# vertex being within distance 4 of A_e and of B_e. The annealer minimises the
# number of unreached vertices from those two sources.
# ----------------------------------------------------------------------------

def _specs(N, rng):
    """Group specs of order N: cyclic first, then semidirect Z_m x| Z_k with random valid r."""
    specs = [('c', N)]
    others = []
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:2]:
            others.append(('s', m, k, r))
    rng.shuffle(others)
    return specs + others


def _table(spec):
    """Multiplication table (numpy N x N) of a group spec."""
    if spec[0] == 'c':
        N = spec[1]
        X = np.arange(N)
        return (X[:, None] + X[None, :]) % N
    _, m, k, r = spec
    N = m * k
    X = np.arange(N)
    A = X // k
    B = X % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    return ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k


def _cost(MT, invl, S, N):
    """Number of vertices unreached within distance 4 from A_e and from B_e."""
    total = 0
    for start in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        fr = np.array([0])
        if start == 0:
            visA[0] = True
            side = 0
        else:
            visB[0] = True
            side = 1
        for _ in range(4):
            if fr.size == 0:
                break
            nb = np.zeros(N, dtype=bool)
            if side == 0:
                for s in S:
                    nb[MT[s][fr]] = True
                nb &= ~visB
                visB |= nb
                side = 1
            else:
                for s in S:
                    nb[MT[invl[s]][fr]] = True
                nb &= ~visA
                visA |= nb
                side = 0
            fr = np.flatnonzero(nb)
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(M, d, end, rng):
    """Search a connection set S of size d; return (2N, edges) if the lift has diameter <= 4 from the sources."""
    N = M.shape[0]
    MT = np.ascontiguousarray(M.T)
    inv = np.argmax(M == 0, axis=1)
    invl = inv.tolist()
    S = rng.sample(range(N), d)
    c = _cost(MT, invl, S, N)
    T = 1.5
    while c > 0 and time.monotonic() < end:
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = _cost(MT, invl, S2, N)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.05, T * 0.9995)
    if c != 0:
        return None
    edges = []
    for s in S:
        col = M[:, s].tolist()
        edges.extend((x, N + col[x]) for x in range(N))
    return 2 * N, edges


def _lift_sweep(d, D, n_lo, n_hi, deadline, rng, slice_len=1.2):
    """Sweep group orders N upward from n_lo/2; return the largest valid (n, edges) found, or None."""
    best = None
    N = max(n_lo // 2 + 1, d + 1)
    while N * 2 <= n_hi and time.monotonic() < deadline:
        specs = _specs(N, rng)
        for spec in specs[:2]:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_len)
            try:
                M = _table(spec)
                res = _anneal(M, d, end, rng)
            except Exception:
                res = None
            if res is not None:
                n, edges = res
                if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                break
        N += 1
    return best


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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _shortcut(edges, adj, color, spare, d, reach, rng):
    """Add one edge between a random spare vertex and the spare opposite-side vertex that gains most coverage."""
    s = rng.choice(spare)
    nb = set(adj[s])
    best, bg = None, -1
    for v in spare:
        if v == s or color[v] == color[s] or v in nb or len(adj[v]) >= d:
            continue
        g = (reach[v] & ~reach[s]).bit_count()
        if g > bg:
            bg, best = g, v
    if best is None:
        return False
    edges.append((s, best))
    adj[s].append(best)
    adj[best].append(s)
    return True


def _extend(n, edges, d, deadline, rng, max_fails):
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

    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
            fails += 1
            if fails % 2 == 0:
                _shortcut(edges, adj, color, spare, d, reach, rng)
            continue
        x = n
        n += 1
        for s in S:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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
            return True
        return False

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

    # New construction: bi-Cayley voltage lifts over cyclic and semidirect groups,
    # searched by annealing. Orders are swept upward from near the Moore-bound
    # target, so the search aims above the current best. Runs first with a
    # fixed share of the budget; the twin/extension pipeline keeps the rest.
    if D >= 4 and d >= 6:
        try:
            moore = lib.moore_bound(d, D)
            n_lo = max(best[0] + 1, int(0.8 * moore))
            n_hi = moore
            now = time.monotonic()
            lift_deadline = now + 0.4 * (deadline - now)
            res = _lift_sweep(d, D, n_lo, n_hi, lift_deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    # Twin graph on W(d-2) built once, then repeated randomized set-cover
    # extensions. Runs alternate between restarting from the twin base and
    # continuing from the best extension found so far.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
