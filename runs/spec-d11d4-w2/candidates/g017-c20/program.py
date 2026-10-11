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
# Bold construction: two-class-per-side group voltage lifts (p = 2).
#
# Groups G = Z_m x|_r Z_k, |G| = N. Vertices A_i,x and B_j,y (i, j in {0,1},
# x, y in G). Each dart (i, j, g) joins A_i,x to B_j,x*g. Row and column sums
# of the dart-count matrix are d, so every vertex has degree d and the graph
# has 4N vertices. Left multiplication is an automorphism, so diameter <= 4
# holds iff every source A_i,e and B_j,e reaches all 4N vertices within 4 steps.
# Simulated annealing over the dart labels minimises the total uncovered count.
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


def _groups_of_order(N, kmax=12):
    """Return (m, k, r) with m*k = N giving Z_m x|_r Z_k (cyclic when k == 1)."""
    out = [(N, 1, 1)]
    for k in range(2, kmax + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_cost(darts, MULT, INV, N, p):
    """Total number of (source, vertex) pairs not joined by a walk of length <= 4 (0 means diameter <= 4)."""
    S = 2 * p
    R = np.zeros((S, S, N), dtype=bool)
    idx = np.arange(S)
    R[idx, idx, 0] = True
    for _ in range(4):
        new = R.copy()
        for i, j, g in darts:
            new[:, p + j] |= R[:, i][:, MULT[INV[g]]]
            new[:, i] |= R[:, p + j][:, MULT[g]]
        R = new
    return S * S * N - int(R.sum())


def _sa_multi(MULT, INV, N, p, d, a, deadline, rng):
    """Anneal dart labels for dart-count matrix [[a, d-a], [d-a, a]]; return darts or None."""
    counts = {(0, 0): a, (0, 1): d - a, (1, 0): d - a, (1, 1): a}
    used = {key: set() for key in counts}
    darts = []
    for (i, j), c in counts.items():
        for g in rng.sample(range(N), c):
            used[(i, j)].add(g)
            darts.append([i, j, g])
    cur = _lift_cost(darts, MULT, INV, N, p)
    if cur == 0:
        return darts
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T_hi = 0.05 * cur + 1.0
    T_lo = 0.3
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - start) / span)
        T = T_hi * (T_lo / T_hi) ** frac
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        g_new = rng.randrange(N)
        while g_new in used[(i, j)]:
            g_new = rng.randrange(N)
        darts[t] = [i, j, g_new]
        c = _lift_cost(darts, MULT, INV, N, p)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            used[(i, j)].discard(g_old)
            used[(i, j)].add(g_new)
        else:
            darts[t] = [i, j, g_old]
    return darts


def _multi_edges(darts, MULT, N, p):
    """Edges of the lift: A_i,x = i*N+x, B_j,y = (p+j)*N+y, dart (i, j, g) joins x to x*g."""
    edges = []
    for i, j, g in darts:
        col = MULT[g].tolist()
        base_a = i * N
        base_b = (p + j) * N
        edges.extend((base_a + x, base_b + col[x]) for x in range(N))
    return edges


def _multi_search(d, D, nlo, nhi, deadline, rng):
    """Search p = 2 group lifts with group order N in [nlo, nhi]; return the largest valid (n, edges) or None."""
    best = None
    cur_lo = nlo
    for N in range(nlo, nhi + 1):
        if N < cur_lo:
            continue
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for m, k, r in groups:
            now = time.monotonic()
            if now >= deadline:
                return best
            if N < cur_lo:
                break
            slice_len = max(0.8, min(3.0, (deadline - now) / 8.0))
            slice_end = min(deadline, now + slice_len)
            try:
                Nn, MUL, INV = _group_tables(m, k, r)
                MULT = np.ascontiguousarray(MUL.T)
                a = rng.randint(1, d - 1)
                darts = _sa_multi(MULT, INV, Nn, 2, d, a, slice_end, rng)
                if darts is None:
                    continue
                edges = _multi_edges(darts, MULT, Nn, 2)
                n = 4 * Nn
                if lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    cur_lo = Nn + 1
                    break
            except Exception:
                continue
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

    parent_deadline = deadline if D != 4 else t0 + 0.55 * budget
    try:
        p = _parent(d, D, parent_deadline, rng)
        if p is not None and p[0] > best[0]:
            best = p
    except Exception:
        pass

    if D == 4 and d >= 3:
        try:
            nlo = max(d, best[0] // 4 + 1)
            nhi = lib.moore_bound(d, 4) // 4
            if nlo <= nhi:
                g = _multi_search(d, D, nlo, nhi, deadline, rng)
                if g is not None and g[0] > best[0]:
                    best = g
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        fb = lib.haar_graph(d, range(d))
        return fb if lib.is_valid(*fb, d, D) else (2, [(0, 1)])
    return best
