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
    """Try to cover all vertices with R3 balls of s0 plus up to d-1 pool vertices; return the set S or None."""
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

    fails = 0
    while time.monotonic() < deadline and fails < 4000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 4000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool_all = [v for v in spare if color[v] == color[s0]]
            S = None
            for attempt in range(4):
                noise = 0.0 if attempt == 0 else 0.35
                S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
                if S is not None:
                    break
            if S is None:
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
# NEW: bi-regular group lifts searched by annealing on voltages.
#
# A base graph with b vertices per side and multiplicity matrix M (row and
# column sums d) is lifted over a finite group G given by a multiplication
# table T (identity = 0) and inverse table I. Vertex A(i,x) = i*G+x joins
# B(j, x*g) for each voltage g in S[(i,j)]. Left multiplication is an
# automorphism that is transitive on each fibre, so diameter <= D holds iff
# a BFS from the 2b representatives A(i,e), B(j,e) reaches everything.
# The search anneals over voltages to minimise the number of unreached pairs.
# ----------------------------------------------------------------------------

def _circ_matrix(d, b):
    """Balanced circulant multiplicity matrix with all row and column sums d."""
    q, rem = divmod(d, b)
    return [[q + (1 if (j - i) % b < rem else 0) for j in range(b)] for i in range(b)]


def _cyclic_table(G):
    x = np.arange(G, dtype=np.int64)
    T = (x[:, None] + x[None, :]) % G
    I = (-x) % G
    return T, I


def _semidirect_table(m, k, r):
    """Tables for Z_m x| Z_k with (a,b)(c,d) = (a + r^b c, b + d); element coded a*k+b."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    bb = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    P = powers[bb]
    T = ((a[:, None] + P[:, None] * a[None, :]) % m) * k + (bb[:, None] + bb[None, :]) % k
    nb = (-bb) % k
    I = ((-powers[nb] * a) % m) * k + nb
    return T, I


def _group_tables(g):
    if g[0] == "cyc":
        return _cyclic_table(g[1])
    _, m, k, r = g
    return _semidirect_table(m, k, r)


def _semi_picks(G, rng):
    cands = []
    for k in range(2, G // 3 + 1):
        if G % k:
            continue
        m = G // k
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return [("sd", m, k, r) for (m, k, r) in cands[:2]]


def _configs(d, target, rng, cache):
    out = []
    for b in (2, 3, 1):
        if b > d:
            continue
        M = _circ_matrix(d, b)
        mx = max(max(row) for row in M)
        Gmin = -(-target // b)
        for G in range(Gmin, Gmin + 3):
            if G <= mx:
                continue
            groups = [("cyc", G)] + _semi_picks(G, rng)
            for g in groups:
                if g not in cache:
                    cache[g] = _group_tables(g)
                T, I = cache[g]
                out.append((b, G, T, I, M))
    return out


def _build_nbr(cfg, S, d):
    b, G, T, I, M = cfg
    n = 2 * b * G
    nbr = np.empty((n, d), dtype=np.int64)
    xs = np.arange(G, dtype=np.int64)
    for i in range(b):
        col = 0
        for j in range(b):
            k = M[i][j]
            if k == 0:
                continue
            g = np.array(S[(i, j)], dtype=np.int64)
            nbr[i * G:(i + 1) * G, col:col + k] = (b + j) * G + T[xs[:, None], g[None, :]]
            col += k
    for j in range(b):
        col = 0
        for i in range(b):
            k = M[i][j]
            if k == 0:
                continue
            g = np.array(S[(i, j)], dtype=np.int64)
            nbr[(b + j) * G:(b + j + 1) * G, col:col + k] = i * G + T[xs[:, None], I[g][None, :]]
            col += k
    return nbr


def _cost(nbr, n, sources, D):
    """Total number of vertices not reached within D steps, summed over the representative sources."""
    total = 0
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        frontier = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = nbr[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += n - int(seen.sum())
    return total


def _anneal(cfg, d, D, end, rng):
    b, G, T, I, M = cfg
    n = 2 * b * G
    cells = [(i, j) for i in range(b) for j in range(b) if M[i][j] > 0]
    S = {c: rng.sample(range(G), M[c[0]][c[1]]) for c in cells}
    sources = [i * G for i in range(b)] + [(b + j) * G for j in range(b)]
    cur = _cost(_build_nbr(cfg, S, d), n, sources, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        temp = 0.5 * (1.0 - (now - t0) / span) + 0.03
        c = cells[rng.randrange(len(cells))]
        lst = S[c]
        t = rng.randrange(len(lst))
        old = lst[t]
        used = set(lst)
        new = rng.randrange(G)
        while new in used:
            new = rng.randrange(G)
        lst[t] = new
        cand = _cost(_build_nbr(cfg, S, d), n, sources, D)
        if cand <= cur or rng.random() < math.exp(-(cand - cur) / temp):
            cur = cand
        else:
            lst[t] = old
    return S


def _edges_from(cfg, S, d):
    b, G = cfg[0], cfg[1]
    nbr = _build_nbr(cfg, S, d)
    rows = nbr[:b * G].tolist()
    return [(u, v) for u, row in enumerate(rows) for v in row]


def _lift_search(d, D, n_floor, deadline, rng):
    """Search group lifts strictly larger than n_floor; return (n, edges) or None."""
    best = None
    target = n_floor // 2 + 1
    cache = {}
    slice_len = 2.5
    while time.monotonic() < deadline - 0.2:
        cfgs = _configs(d, target, rng, cache)
        if not cfgs:
            break
        for cfg in cfgs:
            now = time.monotonic()
            if now >= deadline - 0.2:
                break
            end = min(deadline - 0.2, now + slice_len)
            S = _anneal(cfg, d, D, end, rng)
            if S is None:
                continue
            b, G = cfg[0], cfg[1]
            n = 2 * b * G
            edges = _edges_from(cfg, S, d)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                target = b * G + 1
                break
    return best


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

    # The lift search is the bold new path for diameter-4 cases.
    lift_case = D == 4 and d >= 3
    parent_deadline = t0 + (0.6 if lift_case else 1.0) * budget
    twin_deadline = t0 + 0.5 * (parent_deadline - t0)

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

    # Twin graph on W(d-2), then greedy set-cover extension using the spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold path: group lifts searched by annealing, aimed above the current best order.
    if lift_case and time.monotonic() < deadline - 1.0:
        try:
            res = _lift_search(d, D, best[0], deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
