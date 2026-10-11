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
# Radius-3 balls and greedy set-cover extension for diameter 4.
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


def _greedy_cover(s0, spare, reach, color, full, d, rng):
    """Try to cover all vertices with R3 balls of same-colour spare vertices starting at s0; return S or None."""
    pool = [v for v in spare if color[v] == color[s0] and v != s0]
    S = [s0]
    unc = full & ~reach[s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best == 0:
            return None
        tied = [pool[i] for i, g in enumerate(gains) if g == best]
        bv = rng.choice(tied)
        S.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
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
    while time.monotonic() < deadline and fails < 400:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        cover = None
        for _ in range(12):
            if time.monotonic() >= deadline:
                break
            s0 = rng.choice(spare)
            cover = _greedy_cover(s0, spare, reach, color, full, d, rng)
            if cover is not None:
                break
        if cover is None:
            fails += 1
            continue
        x = n
        n += 1
        for s in cover:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(cover))
        color.append(1 - color[cover[0]])
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bipartite Haar-type graphs over small non-abelian groups.
#
# Vertices A_x = x and B_y = N + y, with A_x ~ B_{x*s} for s in S (|S| = d).
# Left multiplication is an automorphism, so diameter <= 4 reduces to three
# covering conditions on the group G of order N (P = {s t^-1}, Q = {t^-1 s}):
#   P*S covers G,  P u P*P covers G,  Q u Q*Q covers G.
# We search S by simulated annealing on the total number of uncovered elements.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Multiplication table and inverses of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    A = x // k
    B = x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    table = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    inv = np.argmax(table == 0, axis=1).astype(np.int64)
    return table.astype(np.int64), inv


def _group_options(N, rng):
    """Candidate (m, k, r) with m*k = N giving semidirect products (cyclic group included)."""
    opts = [(N, 1, 1)]
    for k in range(2, min(N, 64) + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            opts.append((m, k, rng.choice(rs)))
    rng.shuffle(opts)
    return opts


def _uncovered(S, table, inv, N):
    """Total number of uncovered group elements over the three covering conditions."""
    S = np.asarray(S, dtype=np.int64)
    Si = inv[S]
    P = np.unique(table[S[:, None], Si[None, :]].ravel())
    Q = np.unique(table[Si[:, None], S[None, :]].ravel())
    X1 = table[np.ix_(P, S)].ravel()
    X2 = np.concatenate([P, table[np.ix_(P, P)].ravel()])
    X3 = np.concatenate([Q, table[np.ix_(Q, Q)].ravel()])
    cost = 0
    for X in (X1, X2, X3):
        mk = np.zeros(N, dtype=bool)
        mk[X] = True
        cost += N - int(mk.sum())
    return cost


def _anneal(N, table, inv, d, deadline, rng):
    """Search a d-element connection set S with full coverage; return S or None."""
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cost = _uncovered(S, table, inv, N)
    best_c, best_S = cost, list(S)
    T = 1.5
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c2 = _uncovered(S, table, inv, N)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_c:
                best_c, best_S = cost, list(S)
        else:
            S[i] = old
        T = max(0.3, T * 0.9995)
    return best_S if best_c == 0 else None


def _haar_edges(N, table, S):
    """Edges of the bipartite Haar-type graph: A_x = x joined to B_{x*s} = N + table[x, s]."""
    edges = []
    for s in S:
        col = table[:, s].tolist()
        edges.extend((x, N + col[x]) for x in range(N))
    return N * 2, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.3 * budget
    ext_deadline = t0 + 0.45 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

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
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, ext_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold phase: group-Haar search for diameter 4, aiming above the current order.
    if D == 4 and d >= 3:
        try:
            N = best[0] // 2 + 1
            hi = lib.moore_bound(d, D) // 2
            while N <= hi and N >= d and time.monotonic() < deadline:
                found = False
                for (m, k, r) in _group_options(N, rng)[:3]:
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    slice_end = min(deadline, now + max(1.0, 0.3 * (deadline - now)))
                    table, inv = _group_table(m, k, r)
                    S = _anneal(N, table, inv, d, slice_end, rng)
                    if S is not None:
                        n2, e2 = _haar_edges(N, table, S)
                        consider(n2, e2)
                        found = True
                        break
                if not found:
                    break
                N += 1
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
