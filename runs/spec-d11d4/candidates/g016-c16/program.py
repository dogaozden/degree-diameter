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
# NEW construction: semiregular bipartite voltage lifts over small groups.
#
# Base graph: a vertices on side A, a on side B, d-regular bipartite multigraph
# given by "darts" (u, v, g). Lift over a group G of order N: A-vertex (u, x)
# is joined to B-vertex (v, x*g) for every dart. The lift is d-regular, bipartite,
# has 2*a*N vertices, and left-multiplication is an automorphism, so the
# diameter is checked from the 2a base vertices only. Darts are searched by
# hill climbing on the total number of vertices beyond distance D.
# ----------------------------------------------------------------------------

def _lift_adj(a, N, mulf, darts):
    """Adjacency lists of the lift of the darts over a group of order N."""
    n = 2 * a * N
    adj = [[] for _ in range(n)]
    for u, v, g in darts:
        base_b = (a + v) * N
        for x in range(N):
            p = u * N + x
            q = base_b + mulf(x, g)
            adj[p].append(q)
            adj[q].append(p)
    return n, adj


def _lift_cost(n, adj, a, N, depth):
    """Total number of vertices not within distance depth of the 2a base representatives (0 = valid)."""
    reach = [1 << v for v in range(n)]
    for _ in range(depth):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - reach[s * N].bit_count() for s in range(2 * a))


def _lift_edges(a, N, mulf, darts):
    """Edge list of the lift, vertex ids: A-vertex (u,x) -> u*N+x, B-vertex (v,y) -> (a+v)*N+y."""
    edges = []
    for u, v, g in darts:
        for x in range(N):
            edges.append((u * N + x, (a + v) * N + mulf(x, g)))
    return 2 * a * N, edges


def _group_choices(N, rng):
    """Cyclic group of order N plus some semidirect products Z_m x| Z_k with m*k = N."""
    out = [lib.cyclic_group(N)]
    for k in range(2, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                out.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return out


def _climb(a, N, d, depth, mulf, rng, t_end):
    """Hill-climb darts of a d-regular base over a group of order N until the lift has diameter <= depth."""
    A = [u for u in range(a) for _ in range(d)]
    B = [v for v in range(a) for _ in range(d)]
    rng.shuffle(B)
    darts, seen = [], set()
    for u, v in zip(A, B):
        g = rng.randrange(N)
        while (u, v, g) in seen:
            g = rng.randrange(N)
        seen.add((u, v, g))
        darts.append((u, v, g))
    m = len(darts)
    n, adj = _lift_adj(a, N, mulf, darts)
    cur = _lift_cost(n, adj, a, N, depth)
    while cur > 0 and time.monotonic() < t_end:
        i = rng.randrange(m)
        ui, vi, gi = darts[i]
        if rng.random() < 0.5:
            j = rng.randrange(m)
            if j == i:
                continue
            uj, vj, gj = darts[j]
            if vi == vj:
                continue
            changes = {i: (ui, vj, gi), j: (uj, vi, gj)}
        else:
            ng = rng.randrange(N)
            if ng == gi:
                continue
            changes = {i: (ui, vi, ng)}
        if any(val in seen for val in changes.values()):
            continue
        orig = {k: darts[k] for k in changes}
        for k in changes:
            seen.discard(orig[k])
        for k, val in changes.items():
            darts[k] = val
            seen.add(val)
        n2, adj2 = _lift_adj(a, N, mulf, darts)
        c2 = _lift_cost(n2, adj2, a, N, depth)
        if c2 <= cur or rng.random() < 0.01:
            cur = c2
        else:
            for val in changes.values():
                seen.discard(val)
            for k in changes:
                darts[k] = orig[k]
                seen.add(orig[k])
    return list(darts) if cur == 0 else None


def _lift_search(d, D, rng, t_end, start_n, moore):
    """Search lifts of growing order until time runs out; return the best valid (n, edges) found or None."""
    best_n = start_n
    found = None
    a_list = [2, 1, 3, 4, 5, 6, 7, 8]
    fails = 0
    k = 0
    while time.monotonic() < t_end - 0.5 and best_n < moore:
        a = a_list[k % len(a_list)]
        k += 1
        N = best_n // (2 * a) + 1          # smallest N with 2*a*N > best_n
        if 2 * a * N > moore:
            fails += 1
            if fails > 4 * len(a_list):
                break
            continue
        fails = 0
        groups = _group_choices(N, rng)
        order, mulf, _ = groups[rng.randrange(len(groups))]
        slice_end = min(t_end, time.monotonic() + 8.0)
        darts = _climb(a, N, d, D, mulf, rng, slice_end)
        if darts is None:
            continue
        n, edges = _lift_edges(a, N, mulf, darts)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n = n
            found = (n, edges)
    return found


# ----------------------------------------------------------------------------
# Previous pipeline (projective plane, quadrangle, twin + extension), kept as a
# strong fallback.
# ----------------------------------------------------------------------------

def _parent(d, D, rng, deadline, consider):
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
            twin_deadline = now + 0.5 * max(0.0, deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass


def _moore(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = _moore(d, D)

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Known constructions get the first share of time.
    try:
        _parent(d, D, rng, t0 + 0.45 * T, consider)
    except Exception:
        pass

    # Voltage-lift search uses the remaining time, and only when not already optimal.
    if best[0] < moore and d >= 2 and D >= 2:
        try:
            res = _lift_search(d, D, rng, t0 + T, best[0], moore)
            if res is not None:
                consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
