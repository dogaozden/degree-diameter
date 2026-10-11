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
    core = P + L
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges, core


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


def _extend(n, edges, d, deadline, rng, max_fails=20000):
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
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= max_fails:
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
# Large-neighbourhood search (LNS) for diameter 4.
# ----------------------------------------------------------------------------

LNS_MAX_REMOVE = 3
LNS_FAILS = 300


def _lns(n, edges, core, d, D, deadline, rng, consider):
    """Run LNS until deadline; report every strict improvement through consider(n, edges)."""
    if not lib.is_valid(n, edges, d, D):
        return
    best_n = n
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        room = cur_n - core
        if room < 1:
            break
        k = rng.randint(1, min(LNS_MAX_REMOVE, room))
        R = set(rng.sample(range(core, cur_n), k))
        mp = {}
        for v in range(cur_n):
            if v not in R:
                mp[v] = len(mp)
        base_e = [(mp[u], mp[v]) for u, v in cur_e if u not in R and v not in R]
        base_n = len(mp)
        sub_deadline = min(deadline, time.monotonic() + 2.0)
        n2, e2 = _extend(base_n, base_e, d, sub_deadline, rng, max_fails=LNS_FAILS)
        if n2 < cur_n:
            continue
        if not lib.is_valid(n2, e2, d, D):
            continue
        if n2 > best_n:
            best_n = n2
            consider(n2, e2)
        if n2 > cur_n or rng.random() < 0.5:
            cur_n, cur_e = n2, e2


# ----------------------------------------------------------------------------
# NEW (bold): bi-Cayley lifts over small non-abelian-capable groups.
#
# Base graph: k vertices A (ids 0..k-1) and k vertices B (ids k..2k-1).
# Each of the d "darts layers" i is a bijection perm_i: A -> B with a group
# voltage volt_i[u]. Lift: (u, x) ~ (perm_i(u), x * volt_i[u]) for every x in G.
# The lift is bipartite and d-regular (up to collisions, which lib validates).
# Left multiplication by a group element is an automorphism, so vertices in one
# fibre are equivalent: diameter <= D iff every base vertex's identity-fibre
# representative reaches everything within D steps.
# ----------------------------------------------------------------------------

def _groups(G):
    """Return (order, mul, inv) for cyclic Z_G and all semidirect Z_m x| Z_t with m*t = G."""
    out = [lib.cyclic_group(G)]
    for t in range(2, G):
        if G % t:
            continue
        m = G // t
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, t, m) != 1 % m:
                continue
            try:
                out.append(lib.semidirect_group(m, t, r))
            except ValueError:
                pass
    return out


def _lift_score(k2, G, mt, adjB, D, limit):
    """Total number of (source, vertex) pairs not reached within D steps from identity fibre sources."""
    N = k2 * G
    total = 0
    for b0 in range(k2):
        seen = bytearray(N)
        s0 = b0 * G
        seen[s0] = 1
        frontier = [s0]
        reached = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                b, y = divmod(x, G)
                row = mt[y]
                for nb, g in adjB[b]:
                    z = nb * G + row[g]
                    if not seen[z]:
                        seen[z] = 1
                        nxt.append(z)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
        if total > limit:
            return total
    return total


def _adj_of(k, d, perm, volt, ginv):
    """Base adjacency: adjB[b] = list of (neighbour base id, group element g) meaning (b,y) ~ (nb, y*g)."""
    adjB = [[] for _ in range(2 * k)]
    for i in range(d):
        for u in range(k):
            v = k + perm[i][u]
            g = volt[i][u]
            adjB[u].append((v, g))
            adjB[v].append((u, ginv[g]))
    return adjB


def _lift_search(d, D, k, G, mt, ginv, deadline, rng):
    """Hill-climb voltages and matchings for a valid lift on 2*k*G vertices; return (n, edges) or None."""
    k2 = 2 * k

    def fresh():
        perm = [rng.sample(range(k), k) for _ in range(d)]
        volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        return perm, volt

    perm, volt = fresh()
    cur = _lift_score(k2, G, mt, _adj_of(k, d, perm, volt, ginv), D, 1 << 60)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        stall += 1
        if stall > 300:
            perm, volt = fresh()
            cur = _lift_score(k2, G, mt, _adj_of(k, d, perm, volt, ginv), D, 1 << 60)
            stall = 0
            continue
        i = rng.randrange(d)
        u = rng.randrange(k)
        if rng.random() < 0.6:
            old = volt[i][u]
            volt[i][u] = rng.randrange(G)
            new = _lift_score(k2, G, mt, _adj_of(k, d, perm, volt, ginv), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                volt[i][u] = old
        else:
            u2 = rng.randrange(k)
            if u2 == u:
                continue
            p = perm[i]
            p[u], p[u2] = p[u2], p[u]
            new = _lift_score(k2, G, mt, _adj_of(k, d, perm, volt, ginv), D, cur)
            if new <= cur:
                if new < cur:
                    stall = 0
                cur = new
            else:
                p[u], p[u2] = p[u2], p[u]

    E = set()
    for i in range(d):
        for u in range(k):
            v = k + perm[i][u]
            g = volt[i][u]
            for y in range(G):
                a = u * G + y
                b = v * G + mt[y][g]
                if a != b:
                    E.add((min(a, b), max(a, b)))
    return k2 * G, sorted(E)


def _lift_phase(d, D, bn, deadline, rng, consider):
    """Repeatedly search bi-Cayley lifts of order above bn until the deadline or the Moore bound."""
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and bn < moore:
        opts = []
        for k in (1, 2, 3, 4):
            G0 = bn // (2 * k) + 1
            for G in range(G0, G0 + 3):
                if 2 * k * G <= moore:
                    opts.append((k, G))
        if not opts:
            break
        k, G = rng.choice(opts)
        groups = _groups(G)
        order, mul, inv = rng.choice(groups)
        mt = [[mul(y, g) for g in range(order)] for y in range(order)]
        ginv = [inv(g) for g in range(order)]
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, (deadline - now) / 3.0))
        res = _lift_search(d, D, k, order, mt, ginv, slice_end, rng)
        if res is not None:
            n, edges = res
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
    parent_deadline = t0 + 0.45 * budget
    lns_deadline = t0 + 0.75 * budget
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

    # Twin graph on W(d-2), then greedy set-cover extension.
    start = None
    core = None
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2, core_v = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, parent_deadline, rng)
            consider(n3, e3)
            start = (n3, e3)
            core = core_v
        except Exception:
            start = None
            core = None

    # Diameter-4 LNS on the extended twin graph.
    if D == 4 and start is not None:
        try:
            _lns(start[0], start[1], core, d, D, lns_deadline, rng, consider)
        except Exception:
            pass

    # Bold branch: bi-Cayley lifts over cyclic and semidirect groups, on all remaining time.
    if D >= 2 and d >= 2:
        try:
            _lift_phase(d, D, best[0], deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
