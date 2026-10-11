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
# Parent pipeline (safe baseline), parameterised by its own time budget.
# ----------------------------------------------------------------------------

def _parent(d, D, rng, t0, budget):
    deadline = t0 + budget
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
            twin_deadline = t0 + 0.35 * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempts = 3
            for a in range(attempts):
                now = time.monotonic()
                if now >= deadline - 0.5:
                    break
                slice_end = now + (deadline - now) / (attempts - a)
                n3, e3 = _extend(n2, e2, d, min(slice_end, deadline), rng)
                consider(n3, e3)
        except Exception:
            pass

    return best


# ----------------------------------------------------------------------------
# Bold new construction: bi-Cayley (Haar-type) graphs over groups.
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_{x*s} for s in S, |S| = d.
# Left translations are automorphisms, transitive on each side, so the
# diameter is <= D iff BFS from a_e and from b_e reaches everything within D.
# Searched by simulated annealing over S for each group order M.
# ----------------------------------------------------------------------------

def _group_table(kind, M):
    """Return (T, IV): T[x][s] = x*s and IV[s] = s^{-1} for the group of order M (identity 0)."""
    if kind == 'cyc':
        T = [[(x + s) % M for s in range(M)] for x in range(M)]
        IV = [(-s) % M for s in range(M)]
    else:  # dihedral of order M (M even): (a,b)*(c,e) = (a + (-1)^b c, b+e), coded 2a+b
        m = M // 2

        def mul(x, y):
            a, b = divmod(x, 2)
            c, e = divmod(y, 2)
            sign = 1 if b == 0 else -1
            return ((a + sign * c) % m) * 2 + (b + e) % 2

        T = [[mul(x, s) for s in range(M)] for x in range(M)]
        IV = [next(t for t in range(M) if T[s][t] == 0) for s in range(M)]
    return T, IV


def _cost(M, T, S, Sinv, D):
    """Number of vertices not reached within D from a_e and from b_e (0 means valid)."""
    total = 0
    N = 2 * M
    for src in (0, M):
        dist = [-1] * N
        dist[src] = 0
        frontier = [src]
        for depth in range(1, D + 1):
            nxt = []
            for v in frontier:
                if v < M:
                    row = T[v]
                    for s in S:
                        w = M + row[s]
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
                else:
                    row = T[v - M]
                    for si in Sinv:
                        w = row[si]
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        total += dist.count(-1)
    return total


def _search(M, T, IV, d, D, rng, t_end):
    """Anneal a connection set S of size d; return S with zero cost, or None before t_end."""
    S = rng.sample(range(M), d)
    cur = _cost(M, T, S, [IV[s] for s in S], D)
    temp = 2.0
    while cur > 0 and time.monotonic() < t_end:
        i = rng.randrange(d)
        g = rng.randrange(M)
        if g in S:
            continue
        S2 = S[:]
        S2[i] = g
        c2 = _cost(M, T, S2, [IV[s] for s in S2], D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur = S2, c2
        temp = max(0.1, temp * 0.9995)
    return S if cur == 0 else None


def _bicayley(d, D, rng, deadline, lo, hi, consider):
    """For group orders M in [lo, hi] (ascending), search for a valid bi-Cayley graph on 2M vertices."""
    M = max(lo, d)
    while M <= hi:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        slice_t = max(1.0, 0.3 * remaining)
        kinds = ['cyc'] + (['dih'] if M % 2 == 0 and M >= 6 else [])
        found = None
        for kind in kinds:
            tend = min(time.monotonic() + slice_t / len(kinds), deadline)
            T, IV = _group_table(kind, M)
            S = _search(M, T, IV, d, D, rng, tend)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, M + T[x][s]) for x in range(M) for s in S]
            consider(2 * M, edges)
        M += 1


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

    best = (0, [])
    try:
        best = _parent(d, D, rng, t0, 0.6 * budget)
    except Exception:
        pass
    if best[0] < 2:
        best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    moore = lib._moore_bound(d, D)
    if best[0] < moore and d >= 2 and D >= 2:
        lo = best[0] // 2 + 1
        hi = moore // 2
        try:
            _bicayley(d, D, rng, deadline, lo, hi, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
