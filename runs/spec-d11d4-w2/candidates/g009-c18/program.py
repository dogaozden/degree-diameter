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
# Parent pipeline (projective plane / GQ / twin + extensions), with fallback.
# ----------------------------------------------------------------------------

def _parent_build(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
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

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best


# ----------------------------------------------------------------------------
# Bold alternative for d = 11, D = 4: bi-Cayley graphs over small groups.
#
# Vertices A_x = x and B_x = N + x for x in G (|G| = N). Connection set S of
# size d gives edges A_x -- B_{x s} for s in S. The graph is bipartite and
# d-regular. Diameter <= 4 holds exactly when
#   SS^-1 u (SS^-1)^2        covers G   (A-A pairs),
#   S^-1S u (S^-1S)^2        covers G   (B-B pairs),
#   S u SS^-1S               covers G   (A-B pairs).
# Order 2N beats the record 1734 once N >= 868 and 1774 once N >= 888.
# Moore bound caps N at 1111.
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    """List of (m, k, r) describing semidirect groups Z_m x| Z_k of order N = m*k."""
    opts = []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            opts.append((m, k, r))
        opts.append((m, k, 1))  # direct product, abelian
    rng.shuffle(opts)
    return opts


def _table(m, k, r):
    """Multiplication table and inverse array for Z_m x|_r Z_k; element (a, b) coded as a*k + b."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    el = np.arange(N, dtype=np.int64)
    a = el // k
    b = el % k
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _climb(M, inv, N, d, deadline, rng):
    """Search for S (d distinct group elements) meeting all three covering conditions; None on timeout."""

    def cost(S):
        Si = inv[S]
        E2 = np.unique(M[np.ix_(S, Si)])
        E4 = M[np.ix_(E2, E2)].ravel()
        ca = np.zeros(N, dtype=bool)
        ca[E2] = True
        ca[E4] = True
        Q2 = np.unique(M[np.ix_(Si, S)])
        Q4 = M[np.ix_(Q2, Q2)].ravel()
        cb = np.zeros(N, dtype=bool)
        cb[Q2] = True
        cb[Q4] = True
        O3 = M[np.ix_(E2, S)].ravel()
        cc = np.zeros(N, dtype=bool)
        cc[S] = True
        cc[O3] = True
        return 3 * N - int(ca.sum()) - int(cb.sum()) - int(cc.sum())

    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = cost(S)
    stall = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return S
        i = rng.randrange(d)
        x = rng.randrange(N)
        if (S == x).any():
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = cost(S2)
        if c2 < cur:
            stall = 0
            S, cur = S2, c2
        elif c2 == cur:
            stall += 1
            S, cur = S2, c2
        else:
            stall += 1
            if rng.random() < 0.01:
                S, cur = S2, c2
        if stall > 4000:
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            cur = cost(S)
            stall = 0
    return None


def _bicayley_graph(M, S, N):
    """Edges A_x -- B_{x s} with A_x = x, B_y = N + y."""
    edges = []
    xs = range(N)
    for s in S.tolist():
        col = M[:, s].tolist()
        edges.extend((x, N + col[x]) for x in xs)
    return 2 * N, edges


def _bicayley_search(d, deadline, rng, floor_n=888, ceil_n=1111):
    """Round-robin over orders N and groups; return the largest valid bi-Cayley graph found, or None."""
    best = None
    lo = floor_n
    state = {}
    while True:
        progressed = False
        restart = False
        for N in range(lo, ceil_n + 1):
            now = time.monotonic()
            if now > deadline - 0.3:
                return best
            if N not in state:
                state[N] = [_group_options(N, rng), 0]
            opts, idx = state[N]
            if idx >= len(opts):
                continue
            state[N][1] += 1
            progressed = True
            m, k, r = opts[idx]
            try:
                M, inv = _table(m, k, r)
                S = _climb(M, inv, N, d, min(deadline - 0.3, now + 0.8), rng)
            except Exception:
                S = None
            if S is None:
                continue
            try:
                n2, e2 = _bicayley_graph(M, S, N)
                if lib.is_valid(n2, e2, d, 4) and (best is None or n2 > best[0]):
                    best = (n2, e2)
            except Exception:
                continue
            # Success at N: only larger orders can improve, so move the floor up.
            lo = N + 1
            restart = True
            break
        if restart:
            continue
        if not progressed or lo > ceil_n:
            return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    if d == 11 and D == 4:
        # Parent first on a shorter budget, then the bold bi-Cayley search.
        best = _parent_build(d, D, rng, t0 + 0.5 * total)
        try:
            cand = _bicayley_search(d, t0 + total, rng)
        except Exception:
            cand = None
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
        if not lib.is_valid(best[0], best[1], d, D):
            return 2, [(0, 1)]
        return best

    return _parent_build(d, D, rng, t0 + total)
