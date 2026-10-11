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
# NEW: group-lift search over non-abelian groups.
#
# Base graph: two vertices (side 0, side 1) joined by d darts with voltages
# S in a finite group G (semidirect Z_m x| Z_k). The lift has 2|G| vertices and
# is d-regular bipartite. Left translation by G is an automorphism acting
# transitively on each side, so diameter <= D is equivalent to: both
# vertices (e,0) and (e,1) reach every vertex within distance D. A local
# search over S minimises the number of unreached vertices from those two
# sources. Every candidate still goes through lib.is_valid before use.
# ----------------------------------------------------------------------------

def _gap(order, mul, S, Sinv, D):
    """Number of (source, target) vertices not within distance D, summed over the two sources (e,0), (e,1)."""
    N = 2 * order
    gap = 0
    for src in (0, order):
        dist = [-1] * N
        dist[src] = 0
        frontier = [src]
        seen = 1
        for depth in range(1, D + 1):
            if not frontier:
                break
            nxt = []
            for v in frontier:
                if v < order:
                    for g in S:
                        w = order + mul(v, g)
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
                else:
                    y = v - order
                    for gi in Sinv:
                        w = mul(y, gi)
                        if dist[w] < 0:
                            dist[w] = depth
                            nxt.append(w)
            seen += len(nxt)
            frontier = nxt
        gap += N - seen
    return gap


def _group_search(order, mul, inv, d, D, deadline, rng):
    """Hill-climb a d-element voltage set S in the group so the lift has diameter <= D; return S or None."""
    if d > order:
        return None
    S = rng.sample(range(order), d)
    Sinv = [inv(g) for g in S]
    cur = _gap(order, mul, S, Sinv, D)
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(order)
        if g in S:
            continue
        T = list(S)
        T[i] = g
        Tinv = list(Sinv)
        Tinv[i] = inv(g)
        val = _gap(order, mul, T, Tinv, D)
        if val <= cur:
            S, Sinv, cur = T, Tinv, val
    return S if cur == 0 else None


def _group_options(order, rng):
    """Return (m, k, r) semidirect-product choices with m*k == order, preferring non-abelian ones."""
    opts = []
    for k in (1, 2, 3, 4, 6):
        if order % k:
            continue
        m = order // k
        if m < 3:
            continue
        if k == 1:
            rs = [1]
        else:
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            rng.shuffle(rs)
            rs = rs[:2]
        for r in rs:
            opts.append((m, k, r))
    rng.shuffle(opts)
    return opts


def _group_phase(d, D, deadline, rng, best_n, consider):
    """Search group lifts with increasing order until time runs out; consider() keeps valid improvements."""
    o = best_n() // 2 + 1
    misses = 0
    while time.monotonic() < deadline - 0.5 and misses < 40:
        opts = _group_options(o, rng)[:3]
        improved = False
        for (m, k, r) in opts:
            now = time.monotonic()
            left = deadline - now
            if left < 0.3:
                break
            slot = min(2.5, left / 3.0)
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            if order <= d:
                continue
            S = _group_search(order, mul, inv, d, D, min(deadline, now + slot), rng)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
            if consider(n, edges):
                improved = True
                break
        if improved:
            misses = 0
            o = best_n() // 2 + 1
        else:
            misses += 1
            o += 1


# ----------------------------------------------------------------------------
# Cyclic Haar-graph search: generic fallback for cases with no structured
# construction. Random connection sets S of size d over Z_m, increasing m.
# ----------------------------------------------------------------------------

def _haar_search(d, deadline, D, rng, consider):
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    structured = False

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            return True
        return False

    # Projective plane incidence graph: degree d, diameter 3 (Moore-optimal).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            if consider(*lib.projective_plane_incidence(d - 1)):
                structured = True
        except Exception:
            pass
        if D == 3 and structured:
            return best

    # Twin graph on W(d-2) plus set-cover extension. Capped at 70% of the
    # budget so the group-lift search gets a real share of the time.
    tw_end = t0 + 0.7 * budget
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        attempts = 4
        for attempt in range(attempts):
            now = time.monotonic()
            rem = tw_end - now
            if rem < 3.0:
                break
            share = rem / (attempts - attempt)
            tw_dl = now + share * 0.4
            ex_dl = now + share
            try:
                n2, e2 = _twin_graph(q, tw_dl, rng)
                if consider(n2, e2):
                    structured = True
                n3, e3 = _extend(n2, e2, d, ex_dl, rng)
                if consider(n3, e3):
                    structured = True
            except Exception:
                pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 and time.monotonic() < deadline:
        try:
            if consider(*_gq_incidence(d - 1)):
                structured = True
        except Exception:
            pass

    # New construction: non-abelian group lifts of the two-vertex base graph,
    # searched for orders just above the current best.
    if D >= 2 and d >= 2 and time.monotonic() < deadline - 1.0:
        try:
            _group_phase(d, D, deadline, rng, lambda: best[0], consider)
            if best[0] > 0:
                structured = True
        except Exception:
            pass

    # No structured construction succeeded: spend remaining time on cyclic Haar lifts.
    if not structured and time.monotonic() < deadline:
        _haar_search(d, deadline, D, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
