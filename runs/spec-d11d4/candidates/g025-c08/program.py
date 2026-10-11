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
# New construction: bi-Cayley (2+2 base) lifts over finite groups, found by
# hill-climbing on the number of vertex pairs at distance > 4.
#
# Base graph: a0, a1 (side A), b0, b1 (side B). Multiplicities
# M = [[a, d-a], [d-a, a]] give every base vertex degree d. Each dart
# (u, v, g) lifts to edges (u,x)-(v, x*g). Left multiplication by any group
# element is an automorphism, so the diameter is exactly the maximum
# eccentricity of the four vertices (u, identity), u = 0..3.
# ----------------------------------------------------------------------------

_MT_CACHE = {}


def _group_table(key):
    """Return (order, mt, mul) for the semidirect group key = (m, k, r), with mt[x][y] = x*y."""
    if key not in _MT_CACHE:
        if len(_MT_CACHE) > 40:
            _MT_CACHE.clear()
        order, mul, _ = lib.semidirect_group(*key)
        mt = [[mul(x, y) for y in range(order)] for x in range(order)]
        _MT_CACHE[key] = (order, mt, mul)
    return _MT_CACHE[key]


def _group_candidates(G):
    """Return keys (m, k, r) with m*k = G describing semidirect products Z_m x| Z_k (k=1 gives cyclic)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _bad_pairs_lift(G, mt, darts):
    """Count pairs at distance > 4 witnessed from the four base sources (lower-bounds the diameter defect)."""
    n = 4 * G
    adj = [[] for _ in range(n)]
    for u, v, g in darts:
        ub = u * G
        vb = v * G
        for x in range(G):
            p = ub + x
            q = vb + mt[x][g]
            adj[p].append(q)
            adj[q].append(p)
    bad = 0
    for u in range(4):
        s = u * G
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(4):
            nxt = []
            for w in frontier:
                for z in adj[w]:
                    if not seen[z]:
                        seen[z] = 1
                        nxt.append(z)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += n - cnt
    return bad


def _search_lift(G, mt, d, deadline, rng):
    """Hill-climb voltages for a 2+2 base lift of order 4G; return the darts if diameter <= 4, else None."""
    a = rng.randint(0, d)
    M = [[a, d - a], [d - a, a]]
    darts = []
    for i in range(2):
        for j in range(2):
            for _ in range(M[i][j]):
                darts.append([i, 2 + j, rng.randrange(G)])
    if not darts:
        return None
    cur = _bad_pairs_lift(G, mt, darts)
    while cur > 0 and time.monotonic() < deadline:
        t = rng.randrange(len(darts))
        old = darts[t][2]
        darts[t][2] = rng.randrange(G)
        c = _bad_pairs_lift(G, mt, darts)
        if c <= cur:
            cur = c
        else:
            darts[t][2] = old
    return [tuple(x) for x in darts] if cur == 0 else None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
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

    # Parent pipeline (twin graph + set-cover extension) gets a fraction of the
    # budget; the remainder goes to the lift search below.
    pfrac = 0.6 if D >= 4 else 1.0
    pdl = t0 + pfrac * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            twin_deadline = t0 + 0.4 * pfrac * budget
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            attempt = 0
            while time.monotonic() < pdl - 1.0 and attempt < 4:
                remaining = pdl - time.monotonic()
                slice_end = time.monotonic() + max(1.0, remaining / (4 - attempt))
                n3, e3 = _extend(n2, e2, d, min(slice_end, pdl), rng)
                consider(n3, e3)
                attempt += 1
                if n3 == n2 and attempt >= 2:
                    break
        except Exception:
            pass

    # Bold branch: bi-Cayley lifts over semidirect products, targeting a
    # 4G-vertex graph strictly larger than the current best.
    if D >= 4 and d >= 3:
        while time.monotonic() < deadline - 1.0:
            try:
                G = best[0] // 4 + 1
                cands = _group_candidates(G)
                if not cands:
                    break
                key = rng.choice(cands)
                order, mt, mul = _group_table(key)
                now = time.monotonic()
                slice_end = min(deadline, now + max(2.0, (deadline - now) / 3.0))
                darts = _search_lift(order, mt, d, slice_end, rng)
                if darts is not None:
                    n4, e4 = lib.group_lift(4, darts, order, mul)
                    consider(n4, e4)
            except Exception:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
