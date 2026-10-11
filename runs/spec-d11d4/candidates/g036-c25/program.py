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
# Randomized greedy set-cover vertex extension for diameter 4.
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
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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
# Bold alternative for D = 4: bi-Cayley graphs over small non-cyclic groups.
#
# Base graph: one A-vertex and one B-vertex joined by d darts labelled by a
# connection set S in a group G of order N. The lift has vertices A_x, B_x
# (x in G), edges A_x -- B_{x*g} for g in S. The graph is bipartite, d-regular,
# and vertex-transitive on each side, so diameter <= 4 holds iff every vertex
# is within distance 4 of A_e and of B_e. Those are two BFS runs, vectorized
# with numpy. S is found by simulated annealing on the number of uncovered
# vertices. Every hit is re-verified with lib.is_valid.
# ----------------------------------------------------------------------------

SLICE = 0.8      # seconds of annealing per (group, order) job
ANNEAL_T = 0.6


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k+b (same formula as lib.semidirect_group)."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + E) % k


def _count(table, S, Sinv, side):
    """Number of vertices (both sides) within distance 4 of the start vertex identity on `side`."""
    N = table.shape[0]
    seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    seen[side][0] = True
    frontier = np.array([0], dtype=np.int64)
    total = 1
    cur = side
    for _ in range(4):
        Sarr = S if cur == 0 else Sinv
        nb = np.unique(table[np.ix_(frontier, Sarr)])
        other = 1 - cur
        new = nb[~seen[other][nb]]
        if new.size == 0:
            break
        seen[other][new] = True
        total += int(new.size)
        frontier = new
        cur = other
    return total


def _cost(table, inv, S):
    N = table.shape[0]
    Sinv = inv[S]
    return 4 * N - _count(table, S, Sinv, 0) - _count(table, S, Sinv, 1)


def _anneal(table, inv, d, deadline, rng):
    """Search a connection set of size d; return it as a numpy array, or None if the deadline passes."""
    N = table.shape[0]
    S = rng.sample(range(N), d)
    cur = _cost(table, inv, np.array(S, dtype=np.int64))
    while True:
        if cur == 0:
            return np.array(S, dtype=np.int64)
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(table, inv, np.array(S2, dtype=np.int64))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / ANNEAL_T):
            S, cur = S2, c2


def _make_jobs(lo, hi, rng):
    """Candidate (N, m, k, r) groups Z_m x|_r Z_k with m*k = N, for lo <= N <= hi, shuffled."""
    jobs = []
    for N in range(lo, hi + 1):
        for k in range(1, N // 2 + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            if k == 1:
                jobs.append((N, m, 1, 1))
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            picks = {1}
            if rs:
                picks.update(rng.sample(rs, min(2, len(rs))))
            for r in picks:
                jobs.append((N, m, k, r))
    rng.shuffle(jobs)
    return jobs


def _bicayley_search(d, D, lo, hi, deadline, rng, best_n):
    """Return (n, edges) with n > best_n from a bi-Cayley lift, or None."""
    best = None
    best_N = best_n // 2
    for N, m, k, r in _make_jobs(lo, hi, rng):
        now = time.monotonic()
        if now >= deadline:
            break
        if N <= best_N:
            continue
        table = _table(m, k, r)
        inv = np.argmax(table == 0, axis=1)
        S = _anneal(table, inv, d, min(deadline, now + SLICE), rng)
        if S is None:
            continue
        edges = []
        for g in S:
            col = table[:, int(g)].tolist()
            for x in range(N):
                edges.append((x, N + int(col[x])))
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_N = N
    return best


# ----------------------------------------------------------------------------

def _parent(d, D, rng, t0, budget):
    """Parent pipeline (projective plane / W(q) / twin graph + extension) with its own time budget."""
    deadline = t0 + budget

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

    # Twin graph on W(d-2) (degree d), then randomized set-cover extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.4 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < deadline - 1.0 and attempt < 4:
                remaining = deadline - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    target = (d == 11 and D == 4)
    parent_budget = 0.55 * budget if target else budget

    try:
        best = _parent(d, D, rng, t0, parent_budget)
    except Exception:
        best = lib.haar_graph(d, range(d))

    if target:
        try:
            res = _bicayley_search(d, D, 888, 1000, t0 + budget, rng, best[0])
            if res is not None and res[0] > best[0]:
                best = res
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
