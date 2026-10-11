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
# Greedy set-cover vertex extension for diameter 4 (randomized).
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
# New construction: bi-Cayley (Haar-type) graphs over groups Z_m x|_r Z_k.
#
# Vertices a_x and b_y (x, y in G, |G| = M). Connection set S (|S| = d):
# a_x ~ b_{xs} for s in S. Left multiplication by t is an automorphism, so the
# graph has degree d, is bipartite, and has diameter <= D iff the radius-D
# balls of a_e and b_e cover all 2M vertices. A random search over S with
# hill climbing on the number of uncovered vertices looks for such S, for
# group orders just above the current best half-order.
# ----------------------------------------------------------------------------

def _sem_group(m, k, r):
    """Return (M, col, inv): col(g) is the numpy array of x*g over all x; inv(x) is the scalar inverse."""
    powers = [pow(r, b, m) for b in range(k)]
    pw = np.array(powers, dtype=np.int64)
    M = m * k
    xs = np.arange(M, dtype=np.int64)
    A = xs // k
    B = xs % k
    cache = {}

    def col(g):
        arr = cache.get(g)
        if arr is None:
            c, dd = divmod(g, k)
            arr = ((A + pw[B] * c) % m) * k + (B + dd) % k
            cache[g] = arr
        return arr

    def inv(x):
        a, b = divmod(x, k)
        nb = (-b) % k
        return ((-powers[nb] * a) % m) * k + nb

    return M, col, inv


def _cover_cost(M, col, inv, S, D):
    """Number of (source, vertex) pairs NOT within distance D from a_e or from b_e (0 iff valid)."""
    cols = [col(s) for s in S]
    icols = [col(inv(s)) for s in S]
    total = 0
    for src in (0, M):  # a_e and b_e (identity has code 0)
        visited = np.zeros(2 * M, dtype=bool)
        visited[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            fa = frontier[frontier < M]
            fb = frontier[frontier >= M] - M
            outs = []
            if fa.size:
                for c in cols:
                    outs.append(M + c[fa])
            if fb.size:
                for c in icols:
                    outs.append(c[fb])
            if not outs:
                break
            nxt = np.unique(np.concatenate(outs))
            nxt = nxt[~visited[nxt]]
            if nxt.size == 0:
                break
            visited[nxt] = True
            frontier = nxt
        total += 2 * M - int(visited.sum())
    return total


def _search_group(M, col, inv, d, D, deadline, rng, steps):
    """Hill-climb a connection set S of size d; return (S, cost) with S None unless cost is 0."""
    S = rng.sample(range(M), d)
    cur = _cover_cost(M, col, inv, S, D)
    it = 0
    while cur > 0 and it < steps and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        g = rng.randrange(M)
        if g in S:
            continue
        T = list(S)
        T[i] = g
        c = _cover_cost(M, col, inv, T, D)
        if c <= cur or rng.random() < 0.005:
            S, cur = T, c
    return (S if cur == 0 else None), cur


def _random_group(M0, d, rng):
    """Sample a semidirect group Z_m x|_r Z_k of order M >= M0 (k = 1 is cyclic). Return (M, col, inv)."""
    k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
    m = -(-M0 // k) + rng.randint(0, 2)
    m = max(m, 2)
    while m * k < d + 1:
        m += 1
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(cands) if cands else 1
    return _sem_group(m, k, r)


def _group_search(d, D, best_n, deadline, rng, consider):
    """Search bi-Cayley graphs with ever-larger group orders; pass each valid one to consider()."""
    cap = lib.moore_bound(d, D) // 2
    M0 = best_n // 2 + 1
    while time.monotonic() < deadline and M0 <= cap:
        M, col, inv = _random_group(M0, d, rng)
        if M > cap:
            M0 = max(M0 + 1, cap)  # try again with a smaller target
            continue
        S = None
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            S, _c = _search_group(M, col, inv, d, D, deadline, rng, steps=1500)
            if S is not None:
                break
        if S is not None:
            edges = []
            for s in S:
                c = col(s).tolist()
                edges.extend((x, M + c[x]) for x in range(M))
            consider(2 * M, edges)
            M0 = M + 1


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

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Parent pipeline: twin graph on W(d-2), then randomized set-cover extension.
    parent_end = t0 + 0.65 * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.3 * budget, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_end, rng)
            consider(n3, e3)
        except Exception:
            pass

    # New construction: bi-Cayley search over semidirect groups for the remaining time.
    # Skipped automatically when the graph already meets the Moore bound (calibration cases).
    if D >= 3 and d >= 3 and best[0] < lib.moore_bound(d, D):
        try:
            _group_search(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
