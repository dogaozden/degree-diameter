import itertools
import math
import random
import time

import lib


# ============================================================================
# Legacy construction (previous best program), kept as a safe fallback.
# ============================================================================

def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bad(n, adj, D):
    return sum(n - b.bit_count() for b in _balls_radius(n, adj, D)) // 2


def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so that each resource u is used by at most cap[u] chosen candidates."""
    k = len(R)
    if k == 0:
        return []
    users = [[] for _ in range(n)]
    for i, r in enumerate(R):
        for u in r:
            users[u].append(i)
    load = [0] * n
    inS = [False] * k
    S = set()

    def add(i):
        inS[i] = True
        S.add(i)
        for u in R[i]:
            load[u] += 1

    def remove(i):
        inS[i] = False
        S.discard(i)
        for u in R[i]:
            load[u] -= 1

    order = list(range(k))
    rng.shuffle(order)
    for i in order:
        if all(load[u] < cap[u] for u in R[i]):
            add(i)
    best = list(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        if inS[i]:
            continue
        removed = []
        for u in R[i]:
            while load[u] >= cap[u]:
                j = rng.choice([x for x in users[u] if inS[x]])
                remove(j)
                removed.append(j)
        add(i)
        delta = 1 - len(removed)
        if delta < 0 and rng.random() >= 0.03:
            remove(i)
            for j in removed:
                add(j)
        if len(S) > len(best):
            best = list(S)
    return best


def _exact_cover(R, universe, users, deadline, node_cap):
    """Find candidates whose resource sets partition `universe` exactly (DFS, node-limited)."""
    covered = set()
    chosen = []
    nodes = [0]

    def rec():
        if len(covered) == len(universe):
            return True
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > deadline:
            return False
        best_opts = None
        for u in universe:
            if u in covered:
                continue
            opts = [i for i in users[u] if all(r not in covered for r in R[i])]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        for i in best_opts:
            for r in R[i]:
                covered.add(r)
            chosen.append(i)
            if rec():
                return True
            chosen.pop()
            for r in R[i]:
                covered.discard(r)
        return False

    return list(chosen) if rec() else None


def _twin_pass(n, edges, d, side, rng, deadline, iters):
    """Twin as many vertices of one side as the spare degree of the other side allows."""
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adj[v] and all(capv[u] >= 1 for u in adj[v])]
    if not cands:
        return n, edges
    R = [adj[v] for v in cands]
    universe = sorted({u for r in R for u in r})

    chosen = None
    if all(capv[u] == 1 for u in universe):
        users = [[] for _ in range(n)]
        for i, r in enumerate(R):
            for u in r:
                users[u].append(i)
        ex = _exact_cover(R, universe, users, deadline, 3000)
        if ex is not None:
            chosen = ex
    pk = _pack(R, capv, n, rng, deadline, iters)
    if chosen is None or len(pk) > len(chosen):
        chosen = pk
    if not chosen:
        return n, edges

    new_edges = list(edges)
    nn = n
    for i in chosen:
        v = cands[i]
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        for attempt in range(30):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                break
        if chosen:
            v = n
            new_edges = list(edges)
            for s in chosen:
                new_edges.append((s, v))
            return n + 1, new_edges
    return None


def _fill(n, edges, d, D, rng, deadline):
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _move(cn, ce, d, D, rng, deadline, targeted):
    if targeted:
        best_x, best_b = None, None
        for _ in range(6):
            x = rng.randrange(cn)
            n2, e2 = _remove_vertex(cn, ce, x)
            b = _bad(n2, _adjacency(n2, e2), D)
            if best_b is None or b < best_b:
                best_x, best_b = x, b
        x = best_x
    else:
        x = rng.randrange(cn)
    rn, re = _remove_vertex(cn, ce, x)
    if rn <= 1:
        return None
    if not lib.within_diameter(rn, re, D):
        re = _saturate_edges(rn, re, d, rng)
        if not lib.within_diameter(rn, re, D):
            return None
    return _fill(rn, re, d, D, rng, deadline)


def _ils(n, edges, d, D, deadline, rng, holder):
    cn, ce = n, list(edges)
    stale = 0
    while time.monotonic() < deadline:
        if stale > 400:
            cn, ce = holder[0][0], list(holder[0][1])
            stale = 0
        cand = _move(cn, ce, d, D, rng, deadline, rng.random() < 0.4)
        if cand is None:
            stale += 1
            continue
        rn, re = cand
        if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
            holder[0] = (rn, re)
            cn, ce = rn, re
            stale = 0
            continue
        stale += 1
        floor = holder[0][0] - 2
        if rn >= cn or (rn == cn - 1 and rn >= floor and rng.random() < 0.05):
            cn, ce = rn, re


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    expand_deadline = start + 0.15 * T
    search_deadline = start + 0.90 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    if best[0] >= lib.moore_bound(d, D):
        return best

    bases = []
    if D == 3:
        bases = _best_pg(d, 2)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            try:
                bases.append(_gq_w(q))
            except Exception:
                pass

    for b in bases:
        consider(b[0], b[1])

    rot = 0
    fails = 0
    while bases and time.monotonic() < expand_deadline and fails < 8:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        before = best[0]
        try:
            n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
            consider(n2, e2)
        except Exception:
            break
        if best[0] == before:
            fails += 1

    if best[0] >= lib.moore_bound(d, D):
        return best
    if time.monotonic() < search_deadline and best[0] >= 2:
        holder = [best]
        try:
            _ils(best[0], best[1], d, D, search_deadline, rng, holder)
        except Exception:
            pass
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ============================================================================
# New construction: bipartite voltage lifts over small base graphs and
# finite groups (semidirect products Z_m x| Z_k). The lift of a base with
# k A-vertices and k B-vertices, with d darts per base vertex, has 2*k*m
# vertices. Vertex-transitivity on each fibre means diameter <= D is checked
# by BFS from one representative per base vertex. Search is a hill climb on
# the number of unreached (representative, vertex) pairs.
# ============================================================================

def _g_groups(m, rng, cap=6):
    """Multiplication/inverse tables for several semidirect products of order m."""
    out = []
    for mp in range(1, m + 1):
        if m % mp:
            continue
        k = m // mp
        if mp == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, mp)
                  if math.gcd(r, mp) == 1 and pow(r, k, mp) == 1]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                _, mul, inv = lib.semidirect_group(mp, k, r)
            except ValueError:
                continue
            T = [[mul(x, y) for y in range(m)] for x in range(m)]
            INV = [inv(x) for x in range(m)]
            out.append((T, INV))
    rng.shuffle(out)
    return out[:cap]


def _g_random_darts(k, m, d, rng):
    slots = [j for j in range(k) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for i in range(k):
        for t in range(d):
            j = slots[i * d + t]
            g = rng.randrange(m)
            tries = 0
            while (i, j, g) in seen and tries < 100:
                g = rng.randrange(m)
                tries += 1
            if (i, j, g) in seen:
                return None
            seen.add((i, j, g))
            darts.append([i, j, g])
    return darts


def _g_neighbor(darts, k, m, rng):
    """Change one dart's group label, or swap the base endpoints of two darts.

    Both moves preserve every base degree. Returns None if the move breaks
    the uniqueness of (i, j, g) triples.
    """
    nd = [list(x) for x in darts]
    if k == 1 or rng.random() < 0.5:
        t = rng.randrange(len(nd))
        nd[t][2] = rng.randrange(m)
    else:
        t, u = rng.sample(range(len(nd)), 2)
        if nd[t][1] == nd[u][1]:
            return None
        nd[t][1], nd[u][1] = nd[u][1], nd[t][1]
    s = set()
    for i, j, g in nd:
        key = (i, j, g)
        if key in s:
            return None
        s.add(key)
    return nd


def _g_adj(k, m, T, INV, darts):
    Aout = [[] for _ in range(k)]
    Bin = [[] for _ in range(k)]
    for i, j, g in darts:
        Aout[i].append((j, g))
        Bin[j].append((i, g))
    N = 2 * k * m
    adj = [None] * N
    for i in range(k):
        for x in range(m):
            Tx = T[x]
            adj[i * m + x] = [(k + j) * m + Tx[g] for j, g in Aout[i]]
    for j in range(k):
        for y in range(m):
            Ty = T[y]
            adj[(k + j) * m + y] = [i * m + Ty[INV[g]] for i, g in Bin[j]]
    return adj


def _g_bad(k, m, adj, D):
    """Sum over base representatives of the number of vertices at distance > D."""
    N = 2 * k * m
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    total = 0
    for r in reps:
        seen = bytearray(N)
        seen[r] = 1
        frontier = [r]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _g_climb(N, d, D, deadline, rng, cache):
    """Hill-climb until a lift on N vertices has diameter <= D, or time runs out."""
    if N // 2 < d:
        return None
    ks = [k for k in range(1, 7) if N % (2 * k) == 0]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        m = N // (2 * k)
        if m not in cache:
            cache[m] = _g_groups(m, rng)
        groups = cache[m]
        if not groups:
            return None
        T, INV = rng.choice(groups)
        darts = _g_random_darts(k, m, d, rng)
        if darts is None:
            continue
        f = _g_bad(k, m, _g_adj(k, m, T, INV, darts), D)
        stale = 0
        while f > 0 and stale < 400 and time.monotonic() < deadline:
            nd = _g_neighbor(darts, k, m, rng)
            if nd is None:
                stale += 1
                continue
            f2 = _g_bad(k, m, _g_adj(k, m, T, INV, nd), D)
            if f2 < f:
                stale = 0
            else:
                stale += 1
            if f2 <= f or rng.random() < 0.01:
                darts, f = nd, f2
        if f == 0:
            return k, m, T, INV, darts
    return None


def _g_edges(k, m, T, darts):
    edges = []
    for i, j, g in darts:
        for x in range(m):
            edges.append((i * m + x, (k + j) * m + T[x][g]))
    return 2 * k * m, edges


def _g_grow(d, D, start_n, deadline, rng):
    """Search for lifts of increasing even order starting at start_n."""
    limit = lib.moore_bound(d, D)
    N = start_n + (start_n % 2)
    cache = {}
    best = None
    while N <= limit and time.monotonic() < deadline - 0.2:
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.5 * (deadline - now)))
        res = _g_climb(N, d, D, slice_end, rng, cache)
        if res is None:
            break
        k, m, T, INV, darts = res
        n, edges = _g_edges(k, m, T, darts)
        if not lib.is_valid(n, edges, d, D):
            break
        best = (n, edges)
        N += 2
    return best


# ============================================================================
# Driver.
# ============================================================================

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = float(time_limit)
    deadline = start + max(0.5, min(0.85 * total, total - 3.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Part 1: legacy construction, with part of the budget (fallback quality).
    try:
        remaining = deadline - time.monotonic()
        cand = _legacy_build(d, D, seed, max(0.2, 0.5 * remaining))
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    # Part 2: voltage-lift search over semidirect groups, above the current best.
    try:
        cand = _g_grow(d, D, best[0] + 1, deadline, rng)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
