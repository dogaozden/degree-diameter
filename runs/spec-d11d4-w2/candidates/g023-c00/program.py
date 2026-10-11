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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
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


def _shortcut(edges, adj, color, spare, d, reach, rng):
    """Add one edge between a random spare vertex and the spare opposite-side vertex that gains most coverage."""
    s = rng.choice(spare)
    nb = set(adj[s])
    best, bg = None, -1
    for v in spare:
        if v == s or color[v] == color[s] or v in nb or len(adj[v]) >= d:
            continue
        g = (reach[v] & ~reach[s]).bit_count()
        if g > bg:
            bg, best = g, v
    if best is None:
        return False
    edges.append((s, best))
    adj[s].append(best)
    adj[best].append(s)
    return True


def _extend(n, edges, d, deadline, rng, max_fails):
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
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
            fails += 1
            if fails % 2 == 0:
                _shortcut(edges, adj, color, spare, d, reach, rng)
            continue
        x = n
        n += 1
        for s in S:
            edges.append((s, x))
            adj[s].append(x)
        adj.append(list(S))
        color.append(1 - color[s0])
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# NEW: Cayley-Haar search over semidirect groups Z_m x| Z_k.
#
# Graph H(G, S): parts A = {a_x}, B = {b_y}, edge a_x ~ b_{x*s} for s in S.
# It is d-regular and bipartite when |S| = d with distinct elements. Left
# multiplication is an automorphism, so every a-vertex is equivalent to a_e
# and every b-vertex to b_e. Diameter <= D therefore holds iff both BFS balls
# from a_e and b_e reach everything within depth D. We search S by simulated
# annealing on the number of unreached vertices.
# ----------------------------------------------------------------------------

def _mult_table(m, k, r):
    """Multiplication table T[x, y] = x*y for Z_m x| Z_k (element (a,b) coded a*k+b; identity 0)."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    xs = np.arange(N, dtype=np.int64)
    a = xs // k
    b = xs % k
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + E) % k


def _group_cands(N, rng):
    """Return up to 8 (m, k, r) semidirect parameter triples with m*k = N, shuffled."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        rs = [r for r in range(1, max(m, 2))
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rs:
            out.append((m, k, r))
    rng.shuffle(out)
    return out[:8]


def _unreached(T, Sa, Si, N, D, side):
    """Number of vertices not within distance D of the identity on the given side."""
    seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    seen[side][0] = True
    front = np.zeros(1, dtype=np.int64)
    cur = side
    for _ in range(D):
        if cur == 0:
            tg = T[front[:, None], Sa[None, :]].ravel()
        else:
            tg = T[front[:, None], Si[None, :]].ravel()
        tg = np.unique(tg)
        tg = tg[~seen[1 - cur][tg]]
        seen[1 - cur][tg] = True
        front = tg
        cur = 1 - cur
        if front.size == 0:
            break
    return 2 * N - int(seen[0].sum()) - int(seen[1].sum())


def _score(T, inv_of, S, N, D):
    """Total unreached count from a_e and b_e; zero iff the Haar graph has diameter <= D."""
    Sa = np.asarray(S, dtype=np.int64)
    Si = inv_of[Sa]
    return _unreached(T, Sa, Si, N, D, 0) + _unreached(T, Sa, Si, N, D, 1)


def _anneal(T, N, d, D, rng, end):
    """Anneal a size-d set S in the group to minimise unreached count; return (S, score)."""
    inv_of = np.argmax(T == 0, axis=1)
    S = rng.sample(range(N), d)
    sc = _score(T, inv_of, S, N, D)
    best_S, best_sc = list(S), sc
    temp = 2.0
    while sc > 0 and time.monotonic() < end:
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        S2 = list(S)
        S2[i] = g
        s2 = _score(T, inv_of, S2, N, D)
        if s2 <= sc or rng.random() < math.exp(-(s2 - sc) / temp):
            S, sc = S2, s2
            if sc < best_sc:
                best_S, best_sc = list(S), sc
        temp = max(0.05, temp * 0.9995)
    return best_S, best_sc


def _haar_edges(T, N, S):
    """Edges a_x ~ b_{x*s} with a_x = x and b_y = N + y."""
    edges = []
    for x in range(N):
        for s in S:
            edges.append((x, N + int(T[x, s])))
    return edges


def _group_search(d, D, moore, min_side, deadline, rng):
    """Search Haar graphs over semidirect groups with side size >= min_side; return (n, edges) or None."""
    found = None
    N = min_side
    max_side = moore // 2
    limit = min_side + 24
    while time.monotonic() < deadline and N <= max_side and N <= limit:
        if N < d:
            N += 1
            continue
        hit = None
        for (m, k, r) in _group_cands(N, rng):
            now = time.monotonic()
            if now >= deadline:
                break
            T = _mult_table(m, k, r)
            slice_end = min(deadline, now + 2.5)
            S, sc = _anneal(T, N, d, D, rng, slice_end)
            if sc == 0:
                edges = _haar_edges(T, N, S)
                if lib.is_valid(2 * N, edges, d, D):
                    hit = (2 * N, edges)
                    break
        if hit is not None:
            found = hit
            limit = N + 24
        N += 1
    return found


# ----------------------------------------------------------------------------
# Parent pipeline (projective plane, GQ, twin extensions), with its own deadline.
# ----------------------------------------------------------------------------

def _parent(d, D, deadline, rng, consider):
    """Run the projective / quadrangle / twin-extension constructions until deadline."""
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
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    consider(n3, e3)
                    stagnant = 0
                else:
                    stagnant += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))
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
            return True
        return False

    moore = lib.moore_bound(d, D)
    group_ok = d >= 2 and D >= 2 and best[0] < moore

    # Parent pipeline gets most of the budget when the group search is applicable.
    parent_deadline = t0 + 0.7 * budget if group_ok else deadline
    _parent(d, D, parent_deadline, rng, consider)

    # New construction: Haar graphs over semidirect groups, aiming above the current best.
    if group_ok and time.monotonic() < deadline - 1.0:
        try:
            min_side = best[0] // 2 + 1
            res = _group_search(d, D, moore, min_side, deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
