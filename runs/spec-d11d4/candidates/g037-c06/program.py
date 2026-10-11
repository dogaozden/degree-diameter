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
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
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
# Bold new construction: lifts over NON-cyclic groups Z_m x|_r Z_k.
#
# Base graph: s vertices on side A (0..s-1) and s on side B (s..2s-1), with d
# perfect matchings, each dart (A-vertex u -> B-vertex p_i(u)) carrying a group
# voltage g. Lift vertex (b, x) is id b*M + x. The lift is bipartite with
# 2sM vertices and degree <= d. Left multiplication by a group element is an
# automorphism, so the diameter is <= D iff BFS from (b, identity) reaches every
# lift vertex within D steps, for each of the 2s base vertices b.
# The search is a hill climb on voltages and matching entries, minimising the
# number of unreached (source, vertex) pairs. The BFS is vectorised with numpy.
# ----------------------------------------------------------------------------

def _group(m, k, r):
    """Return (MUL, invs) for Z_m x|_r Z_k with element (a, b) coded as a*k+b; identity is 0."""
    M = m * k
    xs = np.arange(M, dtype=np.int64)
    a = xs // k
    b = xs % k
    P = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    MUL = (((A + P[B] * C) % m) * k + (B + Dd) % k).astype(np.int64)
    invs = np.argmax(MUL == 0, axis=1).astype(np.int64)
    return MUL, invs


def _groups_of_order(M, rng, cap):
    """Return up to cap candidate (m, k, r) with m*k = M, all cyclic/semidirect types included."""
    cands = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        if k == 1:
            cands.append((m, 1, 1))
            continue
        if m == 1:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:cap]


def _nbr(s, d, M, MUL, invs, perms, gens):
    """Return the (2sM, d) neighbour table of the lift."""
    N = 2 * s * M
    nbr = np.empty((N, d), dtype=np.int64)
    xs = np.arange(M, dtype=np.int64)
    for i in range(d):
        p = perms[i]
        pinv = [0] * s
        for u in range(s):
            pinv[p[u]] = u
        for u in range(s):
            g = gens[i][u]
            nbr[u * M:(u + 1) * M, i] = (s + p[u]) * M + MUL[xs, g]
        for v in range(s):
            u = pinv[v]
            gi = int(invs[gens[i][u]])
            nbr[(s + v) * M:(s + v + 1) * M, i] = u * M + MUL[xs, gi]
    return nbr


def _score(s, M, D, nbr, limit):
    """Total unreached (source, vertex) pairs over the 2s base sources; stops early above limit."""
    N = nbr.shape[0]
    total = 0
    for b in range(2 * s):
        src = b * M
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            seen[nxt] = True
            frontier = nxt
        total += N - int(seen.sum())
        if total > limit:
            return total
    return total


def _edges_of(nbr):
    """Return (n, edges) from a neighbour table."""
    N, d = nbr.shape
    src = np.repeat(np.arange(N, dtype=np.int64), d).tolist()
    dst = nbr.ravel().tolist()
    pairs = set()
    for a, c in zip(src, dst):
        if a != c:
            pairs.add((a, c) if a < c else (c, a))
    return N, sorted(pairs)


def _climb(s, d, D, M, grp, deadline, rng):
    """Hill-climb voltages/matchings for a zero-defect lift on 2sM vertices; return nbr table or None."""
    MUL, invs = grp

    def rand_state():
        perms = [rng.sample(range(s), s) for _ in range(d)]
        gens = [[rng.randrange(M) for _ in range(s)] for _ in range(d)]
        return perms, gens

    perms, gens = rand_state()
    nbr = _nbr(s, d, M, MUL, invs, perms, gens)
    cur = _score(s, M, D, nbr, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 2000:
            perms, gens = rand_state()
            nbr = _nbr(s, d, M, MUL, invs, perms, gens)
            cur = _score(s, M, D, nbr, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(s)
        if rng.random() < 0.7 or s == 1:
            old = gens[i][u]
            gens[i][u] = rng.randrange(M)
            nn = _nbr(s, d, M, MUL, invs, perms, gens)
            new = _score(s, M, D, nn, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
                nbr = nn
            else:
                gens[i][u] = old
        else:
            u2 = rng.randrange(s)
            if u2 == u:
                continue
            p = perms[i]
            p[u], p[u2] = p[u2], p[u]
            nn = _nbr(s, d, M, MUL, invs, perms, gens)
            new = _score(s, M, D, nn, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
                nbr = nn
            else:
                p[u], p[u2] = p[u2], p[u]
    return nbr


def _group_search(d, D, best_n, moore, deadline, rng, consider):
    """Search group lifts of order above best_n until the deadline; return the final best order."""
    while time.monotonic() < deadline:
        options = []
        for s in (2, 3, 4, 5):
            Mmin = best_n // (2 * s) + 1
            Mmax = moore // (2 * s)
            if Mmin <= Mmax:
                options.append((s, Mmin, Mmax))
        if not options:
            break
        s, Mmin, Mmax = rng.choice(options)
        M = rng.randint(Mmin, min(Mmax, Mmin + 4))
        cands = _groups_of_order(M, rng, 6)
        for (m, k, r) in cands:
            now = time.monotonic()
            if now > deadline:
                break
            slice_end = min(deadline, now + 6.0)
            grp = _group(m, k, r)
            nbr = _climb(s, d, D, M, grp, slice_end, rng)
            if nbr is None:
                continue
            n, edges = _edges_of(nbr)
            if n > best_n and lib.is_valid(n, edges, d, D):
                consider(n, edges)
                best_n = n
                break
    return best_n


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.30 * budget
    parent_deadline = t0 + 0.40 * budget
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

    # Twin graph on W(d-2), then randomized set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    # Bold change: non-cyclic group lifts (Z_m x|_r Z_k), searched for orders above the current best.
    if D >= 2 and d >= 3 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        if best[0] < moore:
            try:
                _group_search(d, D, best[0], moore, deadline, rng, consider)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
