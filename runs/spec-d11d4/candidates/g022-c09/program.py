import itertools
import math
import random
import time

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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
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
# NEW: voltage-lift search over semidirect products Z_m x| Z_k.
#
# Base graph: k A-vertices and k B-vertices (k = 1 or 2); M[i][j] darts
# between A_i and B_j, each with a distinct group voltage. Row and column
# sums are d, so the lift is d-regular and bipartite. Left translation by
# the group is an automorphism, so diameter <= D is checked by BFS from one
# representative per base vertex. Voltages are improved by annealing on the
# number of (representative, vertex) pairs within distance D.
# ----------------------------------------------------------------------------

def _reach(adj, s, n, D):
    """Number of vertices within distance D of s."""
    seen = bytearray(n)
    seen[s] = 1
    frontier = [s]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            for w in adj[v]:
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _choose_group(N, rng):
    """Return (m, k, r) with m*k = N giving a semidirect product Z_m x| Z_k."""
    ks = [k for k in (2, 3, 4, 5, 6, 8, 9, 10, 12) if N % k == 0 and N // k >= 2]
    if not ks or rng.random() < 0.3:
        return N, 1, 1
    k = rng.choice(ks)
    m = N // k
    r = 1
    for _ in range(300):
        t = rng.randrange(1, m)
        if math.gcd(t, m) == 1 and pow(t, k, m) == 1 % m:
            r = t
            break
    return m, k, r


def _lift_try(k, M, order, mul, D, iters, deadline, rng):
    """Anneal voltages for a base graph with k+k vertices; return (n, edges) if diameter <= D, else None."""
    nb = 2 * k
    n = nb * order
    full = nb * n
    vol = {}
    for i in range(k):
        for j in range(k):
            c = M[i][j]
            if c > 0:
                vol[(i, j)] = rng.sample(range(order), c)
    keys = list(vol.keys())

    def build_adj():
        adj = [[] for _ in range(n)]
        for (i, j), gs in vol.items():
            v = k + j
            for g in gs:
                for x in range(order):
                    a = i * order + x
                    b = v * order + mul(x, g)
                    adj[a].append(b)
                    adj[b].append(a)
        return adj

    def score(adj):
        return sum(_reach(adj, u * order, n, D) for u in range(nb))

    adj = build_adj()
    cur = score(adj)
    it = 0
    while cur < full and it < iters and time.monotonic() < deadline:
        it += 1
        key = rng.choice(keys)
        gs = vol[key]
        idx = rng.randrange(len(gs))
        used = set(gs)
        g = rng.randrange(order)
        while g in used:
            g = rng.randrange(order)
        old = gs[idx]
        gs[idx] = g
        new_adj = build_adj()
        new = score(new_adj)
        if new >= cur or rng.random() < 0.02:
            cur = new
            adj = new_adj
        else:
            gs[idx] = old
    if cur != full:
        return None
    edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
    return n, edges


def _lift_search(d, D, best_n, deadline, rng, consider):
    """Repeatedly try random semidirect-product lifts until deadline; return the best order found."""
    while time.monotonic() < deadline - 0.5:
        if rng.random() < 0.5:
            k, M = 1, [[d]]
        else:
            x = rng.randint(1, d - 1)
            k, M = 2, [[x, d - x], [d - x, x]]
        base_n = 2 * k
        lo = (best_n + base_n) // base_n
        N = rng.randint(lo, lo + max(3, lo // 10))
        m, kk, r = _choose_group(N, rng)
        order, mul, _ = lib.semidirect_group(m, kk, r)
        res = _lift_try(k, M, order, mul, D, 200, deadline, rng)
        if res is not None:
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                best_n = n
    return best_n


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

    # Parent twin/extension pipeline gets the first part of the budget
    # when the lift search also runs.
    use_lift = (D == 4 and d >= 4)
    parent_deadline = t0 + (0.6 * budget if use_lift else budget)

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.35 * (parent_deadline - t0)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= parent_deadline - 0.5:
                    break
                slice_end = now + (parent_deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, parent_deadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    # New construction: voltage lifts over semidirect products.
    if use_lift:
        try:
            _lift_search(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
