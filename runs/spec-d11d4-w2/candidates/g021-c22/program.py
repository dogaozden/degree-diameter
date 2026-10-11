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


def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob noise."""
    if rng.random() < noise:
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


def _extend(n, edges, d, deadline, rng, noise):
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
                bv = _pick(pool, reach, unc, rng, noise)
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
# NEW HELPER: ruin-and-recreate local search on a diameter-D graph.
#
# State is a dict-of-sets adjacency with stable vertex ids and a fixed
# bipartition colouring. A move deletes 1-3 random vertices ("ruin"), then
# regrows vertices greedily ("recreate"): each new vertex x is attached to a set
# S of same-coloured vertices with spare degree whose radius-(D-1) balls cover
# every vertex, which guarantees all distances to x are <= D. The move is
# accepted when the vertex count does not drop and the full diameter check
# still passes. Sideways moves let the search drift across plateaus.
# ----------------------------------------------------------------------------

def _balls_adj(adj, rounds):
    """Return (idx, reach): idx maps vertex id -> index; reach[i] is the bitmask of vertices within `rounds`."""
    ids = list(adj)
    idx = {v: i for i, v in enumerate(ids)}
    nb = [[idx[u] for u in adj[v]] for v in ids]
    reach = [1 << i for i in range(len(ids))]
    for _ in range(rounds):
        new = []
        for i in range(len(ids)):
            r = reach[i]
            for j in nb[i]:
                r |= reach[j]
            new.append(r)
        reach = new
    return idx, reach


def _recreate(adj, col, nxt, d, rng, deadline, max_fail=3):
    """Greedily add new vertices (ids from nxt upward) using spare degree. Mutates adj/col; returns (nxt, added)."""
    added = 0
    fails = 0
    noise = rng.choice([0.0, 0.2, 0.4])
    while fails < max_fail and time.monotonic() < deadline:
        idx, reach = _balls_adj(adj, 3)
        full = (1 << len(idx)) - 1
        spare = [v for v in adj if len(adj[v]) < d]
        if not spare:
            break
        s0 = rng.choice(spare)
        pool = [v for v in spare if v != s0 and col[v] == col[s0]]
        S = [s0]
        unc = full & ~reach[idx[s0]]
        while unc and len(S) < d and pool:
            if rng.random() < noise:
                useful = [v for v in pool if reach[idx[v]] & unc]
                if not useful:
                    break
                bv = rng.choice(useful)
            else:
                best_g, bv = 0, None
                for v in pool:
                    g = (reach[idx[v]] & unc).bit_count()
                    if g > best_g:
                        best_g, bv = g, v
                if bv is None:
                    break
            S.append(bv)
            unc &= ~reach[idx[bv]]
            pool.remove(bv)
        if unc:
            fails += 1
            continue
        x = nxt
        nxt += 1
        adj[x] = set(S)
        for s in S:
            adj[s].add(x)
        col[x] = 1 - col[s0]
        added += 1
        fails = 0
    return nxt, added


def _relabel_state(adj):
    """Return (n, edges) with compact labels 0..n-1 for the current state."""
    ids = sorted(adj)
    m = {v: i for i, v in enumerate(ids)}
    edges = [(m[u], m[v]) for u in ids for v in adj[u] if u < v]
    return len(ids), edges


def _ruin_recreate(n, edges, d, D, deadline, rng):
    """Improve a valid bipartite graph by ruin-and-recreate moves; return the best valid (n, edges) found."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = {}
    for s in range(n):
        if s in col:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w not in col:
                    col[w] = 1 - col[u]
                    stack.append(w)

    best = (n, edges)
    best_n = n
    cur_adj, cur_col, cur_nxt, cur_n = adj, col, n, n
    while time.monotonic() < deadline:
        if cur_n < 3:
            break
        a = {v: set(s) for v, s in cur_adj.items()}
        c = dict(cur_col)
        k = rng.randint(1, 3)
        victims = rng.sample(list(a), min(k, len(a)))
        for v in victims:
            for u in a[v]:
                a[u].discard(v)
            del a[v]
            del c[v]
        nxt, _ = _recreate(a, c, cur_nxt, d, rng, deadline)
        if len(a) < cur_n:
            continue
        _, reach = _balls_adj(a, D)
        full = (1 << len(a)) - 1
        if any(r != full for r in reach):
            continue
        cur_adj, cur_col, cur_nxt, cur_n = a, c, nxt, len(a)
        if cur_n > best_n:
            best_n = cur_n
            best = _relabel_state(cur_adj)
    return best


# ----------------------------------------------------------------------------
# New construction: bipartite Haar-type lifts over groups Z_m x|_r Z_k.
#
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so with T = S S^{-1}, U = S^{-1} S:
#   A-A pairs  need  G = T T           (distance <= 4 from a_e)
#   B-B pairs  need  G = U U           (distance <= 4 from b_e)
#   A-B pairs  need  G = S u T S       (distance <= 3 from a_e)
# (the b_e -> a_e direction is the inverse of the last condition).
# Simulated annealing over S minimises the number of uncovered group elements.
# ----------------------------------------------------------------------------

def _group_tables(m, k, r):
    """Multiplication table and inverse array of Z_m x|_r Z_k, element (a, b) coded as a*k+b, identity 0."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    MUL = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    INV = np.argmax(MUL == 0, axis=1)
    return N, MUL, INV


def _cost(S, MUL, INV, N):
    """Number of group elements left uncovered by the three distance conditions for connection set S."""
    Sa = np.asarray(S, dtype=np.int64)
    Ia = INV[Sa]
    T = np.unique(MUL[np.ix_(Sa, Ia)])
    U = np.unique(MUL[np.ix_(Ia, Sa)])
    mA = np.zeros(N, dtype=bool)
    mA[MUL[np.ix_(T, T)].ravel()] = True
    mB = np.zeros(N, dtype=bool)
    mB[MUL[np.ix_(U, U)].ravel()] = True
    mC = np.zeros(N, dtype=bool)
    mC[MUL[np.ix_(T, Sa)].ravel()] = True
    mC[Sa] = True
    return int(N - mA.sum()) + int(N - mB.sum()) + int(N - mC.sum())


def _sa_group(MUL, INV, N, d, deadline, rng):
    """Anneal a connection set S of size d until cost 0 (diameter 4 Haar lift) or the deadline."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _cost(S, MUL, INV, N)
    temp = 0.6
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        new = list(S)
        new[i] = x
        c = _cost(new, MUL, INV, N)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S = new
            cur = c
    return S


def _lift_edges(S, MUL, N):
    """Edges a_x - b_{x*s} for s in S, with A = 0..N-1 and B = N..2N-1."""
    edges = []
    for s in S:
        col = MUL[:, s].tolist()
        edges.extend((x, N + col[x]) for x in range(N))
    return edges


def _group_candidates(lo, hi, rng):
    """All (N, m, k, r) with lo <= m*k <= hi for small k, sorted by N (ties shuffled)."""
    out = []
    for k in range(1, 13):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            if k == 1:
                out.append((N, m, 1, 1))
                continue
            for r in range(1, m):
                if pow(r, k, m) == 1 % m and math.gcd(r, m) == 1:
                    out.append((N, m, k, r))
    rng.shuffle(out)
    out.sort(key=lambda t: t[0])
    return out


def _group_search(d, D, lo, hi, deadline, rng):
    """Search group Haar lifts with N in [lo, hi]; return the largest valid (n, edges) found, or None."""
    best = None
    cur_lo = lo
    for N, m, k, r in _group_candidates(lo, hi, rng):
        now = time.monotonic()
        if now >= deadline:
            break
        if N < cur_lo:
            continue
        slice_len = max(0.5, min(4.0, (deadline - now) / 8.0))
        slice_end = min(deadline, now + slice_len)
        try:
            Nn, MUL, INV = _group_tables(m, k, r)
            S = _sa_group(MUL, INV, Nn, d, slice_end, rng)
            if S is None:
                continue
            edges = _lift_edges(S, MUL, Nn)
            n = 2 * Nn
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                cur_lo = Nn + 1
        except Exception:
            continue
    return best


# ----------------------------------------------------------------------------
# Parent pipeline (projective plane / GQ / twin + extension), returns best found.
# ----------------------------------------------------------------------------

def _parent(d, D, deadline, rng):
    best = None

    def consider(n, edges):
        nonlocal best
        if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 3 and lib.is_prime_power(d - 1):
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
        q = d - 2
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(q, now + 0.4 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None:
            attempts = 0
            while time.monotonic() < deadline - 0.5 and attempts < 400:
                remaining = deadline - time.monotonic()
                slice_end = time.monotonic() + max(2.0, remaining / 4.0)
                slice_end = min(slice_end, deadline)
                noise = rng.choice([0.1, 0.25, 0.4])
                try:
                    n3, e3 = _extend(base[0], base[1], d, slice_end, rng, noise)
                    consider(n3, e3)
                except Exception:
                    pass
                attempts += 1
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

    deep = (D == 4 and d >= 3)
    parent_deadline = t0 + 0.4 * budget if deep else deadline
    try:
        p = _parent(d, D, parent_deadline, rng)
        if p is not None and p[0] > best[0]:
            best = p
    except Exception:
        pass

    if deep:
        try:
            rr_deadline = t0 + 0.7 * budget
            r = _ruin_recreate(best[0], best[1], d, D, rr_deadline, rng)
            if r[0] > best[0] and lib.is_valid(r[0], r[1], d, D):
                best = r
        except Exception:
            pass

    if deep:
        try:
            lo = best[0] // 2 + 1
            hi = lib.moore_bound(d, 4) // 2
            if lo <= hi:
                g = _group_search(d, D, lo, hi, deadline, rng)
                if g is not None and g[0] > best[0]:
                    best = g
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        fb = lib.haar_graph(d, range(d))
        if d >= 1 and D >= 2 and lib.is_valid(fb[0], fb[1], d, D):
            return fb
        return 2, [(0, 1)]
    return best
