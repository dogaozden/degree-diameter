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
# Bold new construction: lifts of small bipartite base graphs over NON-ABELIAN
# groups Z_m x| Z_k (element (a,b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d)).
#
# Base: s vertices on side A (ids 0..s-1) and s on side B (ids s..2s-1), joined
# by d perfect matchings, each dart carrying a group voltage. Lift vertex (b, x)
# has global id b*G + x. Edges (u,x)-(v, x*g). Left multiplication is an
# automorphism, so the lift has diameter <= D iff every base vertex's identity
# lift reaches all 2sG vertices within D steps. Search minimises unreached pairs
# by hill climbing on voltages and matchings, using vectorised numpy BFS.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Return (G, MTT, inv): MTT[g, x] = x*g, inv[g] = g^{-1}, for the group Z_m x| Z_k with action r."""
    G = m * k
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) if m > 1 else 0 for j in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    MT = A * k + B
    rows, cols = np.nonzero(MT == 0)
    inv = np.empty(G, dtype=np.int64)
    inv[rows] = cols
    MTT = np.ascontiguousarray(MT.T)
    return G, MTT, inv


def _sample_group(G, rng):
    """Return (m, k, r) with m*k = G, a random semidirect product Z_m x| Z_k (r^k = 1 mod m)."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    k = rng.choice(divs)
    m = G // k
    if m == 1:
        return 1, k, 0
    valid = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rng.choice(valid) if valid else 1
    return m, k, r


def _build_nb(s, G, MTT, inv, perm, volt):
    """Neighbour table NB[id, i] = global id of the neighbour along matching i."""
    d = len(perm)
    NB = np.empty((2 * s * G, d), dtype=np.int64)
    for i in range(d):
        pi = perm[i]
        vi = volt[i]
        for u in range(s):
            v = s + pi[u]
            g = vi[u]
            NB[u * G:(u + 1) * G, i] = v * G + MTT[g]
            NB[v * G:(v + 1) * G, i] = u * G + MTT[int(inv[g])]
    return NB


def _score(s, G, D, NB):
    """Total number of (base source, vertex) pairs not reached within D steps from identity lifts."""
    N = NB.shape[0]
    total = 0
    for b0 in range(2 * s):
        seen = np.zeros(N, dtype=bool)
        src = b0 * G
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = NB[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(seen.sum())
    return total


def _lift_edges(NB):
    """Return the edge list (deduplicated, no self-loops) of the lift."""
    E = set()
    for a, row in enumerate(NB.tolist()):
        for y in row:
            if a < y:
                E.add((a, y))
            elif y < a:
                E.add((y, a))
    return sorted(E)


def _search(d, D, s, G, MTT, inv, deadline, rng):
    """Hill-climb a valid group lift on 2*s*G vertices; return (perm, volt) or None."""

    def fresh():
        perm = [rng.sample(range(s), s) for _ in range(d)]
        volt = [[rng.randrange(G) for _ in range(s)] for _ in range(d)]
        return perm, volt

    def sc(perm, volt):
        return _score(s, G, D, _build_nb(s, G, MTT, inv, perm, volt))

    perm, volt = fresh()
    cur = sc(perm, volt)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            perm, volt = fresh()
            cur = sc(perm, volt)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(s)
        if s == 1 or rng.random() < 0.7:
            old = volt[i][u]
            volt[i][u] = rng.randrange(G)
            new = sc(perm, volt)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(s)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = sc(perm, volt)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]
    return perm, volt


def _group_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search for group lifts of order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    ss = [1, 2, 3, 4, 5, 6]
    while time.monotonic() < deadline and bn < moore:
        feas = [s for s in ss if bn // (2 * s) + 1 <= moore // (2 * s)]
        if not feas:
            break
        s = rng.choice(feas)
        gmin = bn // (2 * s) + 1
        gmax = moore // (2 * s)
        G = gmin + rng.randrange(min(gmax - gmin + 1, 25))
        m, k, r = _sample_group(G, rng)
        Gt, MTT, inv = _group_table(m, k, r)
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, (deadline - now) / 4.0))
        res = _search(d, D, s, Gt, MTT, inv, slice_end, rng)
        if res is None:
            continue
        perm, volt = res
        NB = _build_nb(s, Gt, MTT, inv, perm, volt)
        n = 2 * s * Gt
        edges = _lift_edges(NB)
        if n > bn and lib.is_valid(n, edges, d, D):
            consider(n, edges)
            bn = n
    return bn


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.30 * budget
    parent_deadline = t0 + 0.42 * budget
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

    # Bold new search: lifts over non-abelian groups of small bipartite base graphs.
    if D >= 2 and d >= 2:
        try:
            _group_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
