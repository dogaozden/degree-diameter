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
# Bold change: group-lift search with simulated annealing.
#
# A base graph has `a` vertices on each side and is d-regular: layer i is a
# permutation sigma_i, giving darts (u, sigma_i(u), g_{i,u}) with voltages in a
# finite group G of order N. The lift has 2aN vertices, is bipartite, and has
# degree d. Left multiplication is an automorphism, so distance-<=4 reachability
# only needs checking from one identity vertex per base vertex. The cost is the
# number of unreached (source, target) pairs, and simulated annealing drives it
# to zero. Groups are cyclic or semidirect Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _group_opts(N, cache):
    """Return a list of (mul, inv) for groups of order N: cyclic plus semidirect products."""
    if N in cache:
        return cache[N]
    opts = [lib.cyclic_group(N)[1:]]
    for k in range(2, N // 2 + 1):
        if N % k:
            continue
        m = N // k
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append(lib.semidirect_group(m, k, r)[1:])
    cache[N] = opts
    return opts


def _bad_count(NB, N, a):
    """Total unreached (source, target) pairs within distance 4, over the 2a base sources."""
    T = NB.shape[0]
    bad = 0
    for b in range(2 * a):
        s = b * N
        seen = np.zeros(T, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        cnt = 1
        for _ in range(4):
            nb = NB[front].ravel()
            nb = np.unique(nb[~seen[nb]])
            if nb.size == 0:
                break
            seen[nb] = True
            cnt += nb.size
            front = nb
        bad += T - cnt
    return bad


def _sa(a, d, N, mul, inv, deadline, rng):
    """Anneal voltages/permutations for a d-regular group lift with 2a base vertices. Return (ok, darts)."""
    invs = np.array([inv(g) for g in range(N)], dtype=np.int64)
    Gm = np.array([[rng.randrange(N) for _ in range(a)] for _ in range(d)], dtype=np.int64)
    Vt = np.array([rng.sample(range(a), a) for _ in range(d)], dtype=np.int64)
    Rf = np.zeros((d, a, N), dtype=np.int64)
    Rb = np.zeros((d, a, N), dtype=np.int64)

    def setd(i, u):
        g = int(Gm[i, u])
        ig = int(invs[g])
        Rf[i, u] = [mul(x, g) for x in range(N)]
        Rb[i, u] = [mul(y, ig) for y in range(N)]

    for i in range(d):
        for u in range(a):
            setd(i, u)
    Uinv = np.argsort(Vt, axis=1)

    def cost():
        NA = ((a + Vt)[:, :, None] * N + Rf).transpose(1, 2, 0).reshape(a * N, d)
        Rsel = Rb[np.arange(d)[:, None], Uinv]
        NBv = (Uinv[:, :, None] * N + Rsel).transpose(1, 2, 0).reshape(a * N, d)
        return _bad_count(np.vstack([NA, NBv]), N, a)

    cur = cost()
    while cur > 0 and time.monotonic() < deadline:
        if rng.random() < 0.5:
            i = rng.randrange(d)
            u = rng.randrange(a)
            oldg = int(Gm[i, u])
            oldf = Rf[i, u].copy()
            oldb = Rb[i, u].copy()
            Gm[i, u] = rng.randrange(N)
            setd(i, u)
            new = cost()
            if new <= cur or rng.random() < math.exp(-(new - cur) / max(0.5, 0.03 * cur)):
                cur = new
            else:
                Gm[i, u] = oldg
                Rf[i, u] = oldf
                Rb[i, u] = oldb
        else:
            if a < 2:
                continue
            i = rng.randrange(d)
            u1, u2 = rng.sample(range(a), 2)
            Vt[i, u1], Vt[i, u2] = Vt[i, u2], Vt[i, u1]
            Uinv[i] = np.argsort(Vt[i])
            new = cost()
            if new <= cur or rng.random() < math.exp(-(new - cur) / max(0.5, 0.03 * cur)):
                cur = new
            else:
                Vt[i, u1], Vt[i, u2] = Vt[i, u2], Vt[i, u1]
                Uinv[i] = np.argsort(Vt[i])
    if cur == 0:
        darts = [(u, a + int(Vt[i, u]), int(Gm[i, u])) for i in range(d) for u in range(a)]
        return True, darts
    return False, None


def _lift_search(d, deadline, rng):
    """Search group lifts with growing order; return the largest valid (n, edges) found, or None."""
    T_est = int(0.8 * 2 * sum((d - 1) ** i for i in range(4)))  # 0.8 of the bipartite Moore bound
    cache = {}
    best = None
    alist = [2, 3, 1, 4]
    for idx, a in enumerate(alist):
        now = time.monotonic()
        if now >= deadline:
            break
        a_dl = now + (deadline - now) / (len(alist) - idx)
        N = -(-T_est // (2 * a))
        while time.monotonic() < a_dl:
            opts = _group_opts(N, cache)
            found = False
            for _ in range(3):
                now = time.monotonic()
                if now >= a_dl:
                    break
                sl = max(0.3, (a_dl - now) / 3.0)
                mul, inv = rng.choice(opts)
                ok, darts = _sa(a, d, N, mul, inv, min(a_dl, now + sl), rng)
                if ok:
                    n, edges = lib.group_lift(2 * a, darts, N, mul)
                    if (best is None or n > best[0]) and lib.is_valid(n, edges, d, 4):
                        best = (n, edges)
                    found = True
                    break
            if not found:
                break
            N += 1
    return best


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

    # Parent pipeline first (safe result), using about 60% of the budget.
    parent_dl = t0 + 0.6 * budget

    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_dl = now + 0.5 * max(0.0, parent_dl - now)
            n2, e2 = _twin_graph(d - 2, twin_dl, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_dl, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold search with the remaining time: group lifts, for diameter 4 and degree >= 5.
    if D >= 4 and d >= 5:
        try:
            res = _lift_search(d, deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
