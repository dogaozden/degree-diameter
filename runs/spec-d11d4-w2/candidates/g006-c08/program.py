import itertools
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
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
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
# Haar graphs H(Z_m, S) with |S| = d, searched randomly.
# ----------------------------------------------------------------------------

def _haar_ok(m, S, D):
    """True if the Haar graph on Z_m with connection set S has diameter <= D."""
    A = np.zeros(m, dtype=bool)
    A[0] = True
    B = np.zeros(m, dtype=bool)
    negS = [(-s) % m for s in S]
    for step in range(D):
        Y = np.zeros(m, dtype=bool)
        if step % 2 == 0:
            for s in S:
                Y |= np.roll(A, s)
            B |= Y
        else:
            for t in negS:
                Y |= np.roll(B, t)
            A |= Y
    return bool(A.all() and B.all())


def _haar_search(d, D, m_hi, rng, deadline, trials_per):
    """Binary search for the largest m with a working random Haar graph; return (m, S)."""
    lo, hi = d, max(d, m_hi)
    best = (d, list(range(d)))
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        found = None
        for _ in range(trials_per):
            if time.monotonic() >= deadline:
                break
            S = rng.sample(range(mid), d)
            if _haar_ok(mid, S, D):
                found = S
                break
        if found is not None:
            best = (mid, found)
            lo = mid
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# NEW (bold attempt): Z_m voltage lifts over a k+k base multigraph with d darts
# per base vertex, voltages found by local search. The score is the number of
# (source, vertex) pairs at distance > D from the base fibre representatives.
# Translation invariance makes this exact for the whole lift.
# ----------------------------------------------------------------------------

def _lift_uncovered(m, k, D, darts):
    """Number of (base source, lift vertex) pairs not within distance D; 0 means diameter <= D."""
    S = 2 * k
    balls = np.zeros((S, S, m), dtype=bool)
    idx = np.arange(S)
    balls[idx, idx, 0] = True
    for _ in range(D):
        old = balls
        new = old.copy()
        for i, j, a in darts:
            jj = k + j
            new[:, jj, :] |= np.roll(old[:, i, :], a, axis=-1)
            new[:, i, :] |= np.roll(old[:, jj, :], -a, axis=-1)
        balls = new
    return int(balls.size - np.count_nonzero(balls))


def _random_mult(d, k, rng):
    """k x k nonnegative integer matrix with all row and column sums d (sum of d random permutations)."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    return M


def _random_darts(m, M, rng):
    """Assign distinct voltages in Z_m to the parallel darts of each base pair."""
    darts = []
    for i, row in enumerate(M):
        for j, c in enumerate(row):
            if c:
                for v in rng.sample(range(m), c):
                    darts.append((i, j, v))
    return darts


def _lift_search(d, D, target_n, deadline, rng):
    """Search for a Z_m voltage lift with more than target_n vertices and diameter <= D; return (n, edges) or None."""
    moore = lib._moore_bound(d, D)
    ks = (2, 3, 4)
    for idx, k in enumerate(ks):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(ks) - idx)
        m = max(d, -(-(target_n + 1) // (2 * k)))
        if 2 * k * m > moore:
            continue
        while time.monotonic() < slice_end:
            M = _random_mult(d, k, rng)
            darts = _random_darts(m, M, rng)
            score = _lift_uncovered(m, k, D, darts)
            stall = 0
            while score > 0 and stall < 3000 and time.monotonic() < slice_end:
                t = rng.randrange(len(darts))
                i, j, a = darts[t]
                used = {a2 for (i2, j2, a2) in darts if i2 == i and j2 == j}
                new_a = rng.randrange(m)
                while new_a in used and new_a != a:
                    new_a = rng.randrange(m)
                if new_a == a:
                    stall += 1
                    continue
                trial = darts[:]
                trial[t] = (i, j, new_a)
                s2 = _lift_uncovered(m, k, D, trial)
                if s2 <= score:
                    if s2 < score:
                        stall = 0
                    else:
                        stall += 1
                    darts, score = trial, s2
                else:
                    stall += 1
            if score == 0:
                n, edges = lib.voltage_lift(2 * k, [(i, k + j, a) for i, j, a in darts], m)
                return n, edges
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    # Parent (algebraic/search) phases get most of the budget; the lift attempt gets the rest.
    parent_deadline = t0 + 0.75 * budget
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

    # Phase 1: random Haar graphs on Z_m (degree d, bipartite, diameter D).
    try:
        m_hi = max(d, lib._moore_bound(d, D) // 2)
        m, S = _haar_search(d, D, m_hi, rng, t0 + 0.5 * (parent_deadline - t0), 1500)
        consider(*lib.haar_graph(m, S))
    except Exception:
        pass

    # Phase 2: algebraic constructions.
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
            now = time.monotonic()
            twin_deadline = now + 0.5 * (parent_deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Phase 3 (bold): voltage lifts over small non-cyclic-free base multigraphs.
    # Only attempted when the current best is below the Moore bound.
    if D >= 3 and d >= 3 and best[0] < lib._moore_bound(d, D):
        try:
            res = _lift_search(d, D, best[0], deadline, rng)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
