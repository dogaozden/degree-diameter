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


def _bicolor(n, adj):
    """Return a 2-colouring of every vertex (adj: neighbour sequences)."""
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
    return color


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bicolor(n, adj)

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
# Edge-split growth ("swap-grow"), always validated with lib.is_valid.
# ----------------------------------------------------------------------------

def _swap_grow(n, edges, d, D, deadline, rng):
    """Grow by edge-split moves until the deadline; return (n, edges), always valid."""
    eset = set()
    for u, v in edges:
        eset.add((u, v) if u < v else (v, u))
    adj = [set() for _ in range(n)]
    for u, v in eset:
        adj[u].add(v)
        adj[v].add(u)
    color = _bicolor(n, adj)

    while time.monotonic() < deadline:
        sat = [v for v in range(n) if len(adj[v]) == d]
        if not sat:
            break
        s = rng.choice(sat)
        t = rng.choice(sorted(adj[s]))
        key = (s, t) if s < t else (t, s)
        eset.discard(key)
        adj[s].discard(t)
        adj[t].discard(s)

        reach = _ball3(n, adj)
        unc = ((1 << n) - 1) & ~reach[s]
        pool = [v for v in range(n) if color[v] == color[s] and v != s and len(adj[v]) < d]
        S = [s]
        while unc and len(S) < d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)

        if unc == 0:
            x = n
            adj.append(set())
            color.append(color[t])
            for w in S:
                adj[w].add(x)
                adj[x].add(w)
                eset.add((w, x))
            if lib.is_valid(n + 1, list(eset), d, D):
                n += 1
                continue
            for w in S:
                adj[w].discard(x)
                eset.discard((w, x))
            adj.pop()
            color.pop()

        adj[s].add(t)
        adj[t].add(s)
        eset.add(key)
    return n, sorted(eset)


# ----------------------------------------------------------------------------
# NEW (bold): bipartite group lifts over non-abelian groups.
#
# Base graph: two vertices A, B joined by d parallel darts g in S, where
# S is a set of d group elements containing the identity (WLOG, by relabelling).
# The lift has 2|G| vertices, is d-regular and bipartite. Distance 3 from A to B
# is governed by words s1 s2^-1 s3, so the key condition is that
# S union {s1 s2^-1 s3} covers G. We search S by local search on the number of
# uncovered group elements, then verify the full lift with lib.is_valid.
# ----------------------------------------------------------------------------

def _group_candidates(N, rng, limit):
    """Non-abelian semidirect groups Z_m x| Z_k of order N (r != 1), shuffled, at most limit."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:limit]


def _uncovered(S, order, mul, inv):
    """Number of group elements not in S union {s1 s2^-1 s3}."""
    Si = [inv(s) for s in S]
    cov = set(S)
    for a in S:
        for b in Si:
            ab = mul(a, b)
            for c in S:
                cov.add(mul(ab, c))
    return order - len(cov)


def _lift_search(order, mul, inv, d, rng, deadline):
    """Local search for S (size d, identity included) with zero uncovered elements; None on failure."""
    if order < d:
        return None
    S = [0] + rng.sample(range(1, order), d - 1)
    cur = _uncovered(S, order, mul, inv)
    best_S, best_u = list(S), cur
    T = 0.6
    while cur and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        c = rng.randrange(1, order)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        u = _uncovered(S, order, mul, inv)
        if u <= cur or rng.random() < math.exp(-(u - cur) / T):
            cur = u
            if u < best_u:
                best_u, best_S = u, list(S)
        else:
            S[i] = old
    return best_S if best_u == 0 else None


def _lift_phase(d, D, rng, deadline, consider):
    """Ascending search over group orders N; each success gives a 2N-vertex valid graph."""
    moore = lib.moore_bound(d, D)
    N = max(2, math.ceil(0.4 * moore))
    N_hi = d * (d - 1) ** 2 + d
    while N <= N_hi and time.monotonic() < deadline:
        for m, k, r in _group_candidates(N, rng, 2):
            now = time.monotonic()
            if now >= deadline:
                return
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            S = _lift_search(order, mul, inv, d, rng, min(deadline, now + 1.5))
            if S is not None:
                n, edges = lib.group_lift(2, [(0, 1, s) for s in S], order, mul)
                consider(n, edges)
                break
        N += 1


# ----------------------------------------------------------------------------
# Parent pipeline: twin graph on W(d-2), cover extension, edge-split growth.
# ----------------------------------------------------------------------------

def _parent_pipeline(d, D, rng, consider, end):
    ts = time.monotonic()
    pb = max(1.0, end - ts)
    deadline = ts + pb
    twin_deadline = ts + 0.4 * pb
    extend_deadline = ts + 0.7 * pb

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
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, extend_deadline, rng)
            consider(n3, e3)
            n4, e4 = _swap_grow(n3, e3, d, D, deadline, rng)
            consider(n4, e4)
        except Exception:
            pass


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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

    # Bold branch: non-abelian group lifts (D = 4), with a time slice of 40%.
    if D == 4 and d >= 3:
        try:
            _lift_phase(d, D, rng, t0 + 0.4 * budget, consider)
        except Exception:
            pass

    # Parent construction gets the remaining time.
    try:
        _parent_pipeline(d, D, rng, consider, t0 + budget)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
