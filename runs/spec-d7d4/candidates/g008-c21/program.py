import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


# ----------------------------------------------------------------------------
# Twin augmentation by packing.
# ----------------------------------------------------------------------------

def _twin_packing(n, adj, slack, rng, deadline):
    """Return a list of vertices whose twins can be added together within the slack."""
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and all(load[w] < slack[w] for w in adj[x]):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
            drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(1 for x in cand if inset[x])
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    """Add twins of a packed vertex set. Returns (n, edges); bipartite and diameter-preserving."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (D = 3 only).
# ----------------------------------------------------------------------------

def _pg_data(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving) and edge saturation.
# ----------------------------------------------------------------------------

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


def _exact_cover(cands, ball, full, d, budget):
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


def _extend_cover(n, edges, d, D, deadline, rng, restarts, always_random=False):
    """Add vertices whose neighbourhoods cover everything within distance D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_cover(cands, ball, full, d, 2000)
            if not chosen:
                for attempt in range(restarts):
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
    """Join deficient opposite-side vertices with the leftover spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


def _grow(n, edges, d, D, deadline, rng, restarts=200, always_random=False):
    """Cover extension first, then saturation. Both preserve diameter."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Degree-conserving repair annealing with vertex insertion.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _apply_ops(adj, ops):
    for t, x, y in ops:
        if t == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _undo_ops(adj, ops):
    for t, x, y in reversed(ops):
        if t == 'a':
            adj[x].discard(y)
            adj[y].discard(x)
        else:
            adj[x].add(y)
            adj[y].add(x)


def _propose(N, adj, color, d, rng):
    """Return a list of operations ('a' add / 'd' delete, x, y) or None."""
    r = rng.random()
    if r < 0.4:
        p = rng.randrange(N)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        a, b = (p, q) if color[p] == 0 else (q, p)
        p = rng.randrange(N)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        c, e = (p, q) if color[p] == 0 else (q, p)
        if a == c or b == e or e in adj[a] or b in adj[c]:
            return None
        return [('d', a, b), ('d', c, e), ('a', a, e), ('a', c, b)]
    defs = [[], []]
    for v in range(N):
        if len(adj[v]) < d:
            defs[color[v]].append(v)
    if r < 0.8:
        s = rng.randrange(2)
        if not defs[s]:
            return None
        x = rng.choice(defs[s])
        b = rng.randrange(N)
        if color[b] == s or not adj[b] or b in adj[x]:
            return None
        a = rng.choice(tuple(adj[b]))
        return [('d', a, b), ('a', x, b)]
    if not defs[0] or not defs[1]:
        return None
    x = rng.choice(defs[0])
    y = rng.choice(defs[1])
    if y in adj[x]:
        return None
    return [('a', x, y)]


def _repair_anneal(n, edges, d, D, deadline, rng):
    """Insert one vertex into a valid graph and anneal to diameter D. Returns (n, edges) or None."""
    adj0 = [[] for _ in range(n)]
    for u, v in edges:
        adj0[u].append(v)
        adj0[v].append(u)
    color = _bipartition(n, adj0)
    N = n + 1
    color.append(rng.randrange(2))
    adj = [set(a) for a in adj0] + [set()]

    cur = _bad_count(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 1.0 * (0.03 ** frac)
        ops = _propose(N, adj, color, d, rng)
        if ops is None:
            continue
        _apply_ops(adj, ops)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            _undo_ops(adj, ops)
    out = [(a, b) for a in range(N) if color[a] == 0 for b in adj[a]]
    return N, out


# ----------------------------------------------------------------------------
# NEW: large-neighbourhood search with slot reuse (remove a BFS ball of
# vertices, regrow the same slots plus extra ones with greedy ball-cover
# attachment, then repair the residual bad pairs with degree-safe moves).
# Vertices are kept as slots with an `alive` flag so that removed labels are
# reused; dead slots have no edges, so bad pairs are counted over live slots.
# ----------------------------------------------------------------------------

def _alive_bad(n, adj, alive, D):
    """Bad pairs (distance > D) counted only among alive vertices."""
    mask = 0
    for v in range(n):
        if alive[v]:
            mask |= 1 << v
    L = mask.bit_count()
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    total = 0
    for v in range(n):
        if alive[v]:
            total += L - (reach[v] & mask).bit_count()
    return total // 2


def _lns_remove(adj, alive, center, k, rng):
    """Remove up to k alive vertices in BFS order from center; return the removed list."""
    order = [center]
    seen = {center}
    i = 0
    while i < len(order) and len(order) < k:
        v = order[i]
        i += 1
        nb = list(adj[v])
        rng.shuffle(nb)
        for u in nb:
            if u not in seen and alive[u]:
                seen.add(u)
                order.append(u)
                if len(order) >= k:
                    break
    removed = order[:k]
    for v in removed:
        for u in adj[v]:
            adj[u].discard(v)
        adj[v].clear()
        alive[v] = False
    return removed


def _lns_connect(n, adj, color, alive, d, D, s, rng):
    """Greedily attach fresh vertex s to opposite-side vertices maximising new ball coverage."""
    other = 1 - color[s]
    balls = _balls_radius(n, adj, D - 1)
    target = 0
    for v in range(n):
        if alive[v]:
            target |= 1 << v
    covered = 1 << s
    cands = [u for u in range(n)
             if alive[u] and color[u] == other and u != s and len(adj[u]) < d]
    rng.shuffle(cands)
    while len(adj[s]) < d:
        best_g, best_u = 0, -1
        for u in cands:
            if u in adj[s] or len(adj[u]) >= d:
                continue
            g = (balls[u] & target & ~covered).bit_count()
            if g > best_g:
                best_g, best_u = g, u
        if best_u < 0:
            break
        adj[s].add(best_u)
        adj[best_u].add(s)
        covered |= balls[best_u]


def _lns_propose(live, adj, color, d, rng):
    """Degree-safe moves on live vertices: 2-switch or link of two deficient opposite vertices."""
    if rng.random() < 0.5:
        p = rng.choice(live)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        a, b = (p, q) if color[p] == 0 else (q, p)
        p = rng.choice(live)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        c, e = (p, q) if color[p] == 0 else (q, p)
        if a == c or b == e or e in adj[a] or b in adj[c]:
            return None
        return [('d', a, b), ('d', c, e), ('a', a, e), ('a', c, b)]
    defs0 = [v for v in live if color[v] == 0 and len(adj[v]) < d]
    defs1 = [v for v in live if color[v] == 1 and len(adj[v]) < d]
    if not defs0 or not defs1:
        return None
    x = rng.choice(defs0)
    y = rng.choice(defs1)
    if y in adj[x]:
        return None
    return [('a', x, y)]


def _lns_fix(n, adj, color, alive, d, D, rng, steps, deadline):
    """Hill-climb the alive bad-pair count down with degree-safe moves."""
    live = [v for v in range(n) if alive[v]]
    cur = _alive_bad(n, adj, alive, D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        ops = _lns_propose(live, adj, color, d, rng)
        if not ops:
            continue
        _apply_ops(adj, ops)
        new = _alive_bad(n, adj, alive, D)
        if new <= cur:
            cur = new
        else:
            _undo_ops(adj, ops)
    return cur


def _lns_step(n, adj, color, alive, d, D, rng, k, extra, deadline):
    """One LNS move on copies. Returns the new state if the result is valid, else None."""
    adj = [set(s) for s in adj]
    color = list(color)
    alive = list(alive)
    live = [v for v in range(n) if alive[v]]
    if len(live) <= k + 1:
        return None
    center = rng.choice(live)
    removed = _lns_remove(adj, alive, center, k, rng)
    free = list(removed)
    for _ in range(len(removed) + extra):
        if free:
            s = free.pop()
        else:
            s = n
            n += 1
            adj.append(set())
            color.append(rng.randrange(2))
            alive.append(False)
        alive[s] = True
        _lns_connect(n, adj, color, alive, d, D, s, rng)
    cur = _alive_bad(n, adj, alive, D)
    if cur:
        cur = _lns_fix(n, adj, color, alive, d, D, rng, 40, deadline)
    if cur == 0:
        return n, adj, color, alive
    return None


def _lns_export(n, adj, color, alive):
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    E = [(idx[v], idx[u]) for v in range(n) if alive[v] and color[v] == 0
         for u in adj[v] if alive[u]]
    return len(idx), E


def _lns_search(n0, edges0, d, D, deadline, rng, consider):
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n0, adj)
    alive = [True] * n0
    n = n0
    while time.monotonic() < deadline:
        k = rng.choice([2, 3, 4, 5, 6])
        extra = 1 if rng.random() < 0.8 else 0
        res = _lns_step(n, adj, color, alive, d, D, rng, k, extra, deadline)
        if res is None:
            continue
        n, adj, color, alive = res
        if extra:
            en, ee = _lns_export(n, adj, color, alive)
            consider(en, ee)


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Count (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + (0.55 if D >= 4 else 0.82) * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng, 200)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.35 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.45 * time_limit
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= twin_deadline:
                break
            gq = _gq_w(q)
            consider(gq[0], gq[1])
            share = (twin_deadline - now) / (len(qs) - idx)
            tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
            consider(tn, te)
            n2, e2 = _grow(tn, te, d, D,
                           min(deadline, time.monotonic() + 0.05 * time_limit),
                           rng, 300, False)
            consider(n2, e2)

    # Main search loop.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        r = rng.random()
        if D <= 4 and haar_miss < 4 and r < 0.06:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue
        if D == 4 and r < 0.3:
            short = min(deadline, time.monotonic() + 0.04 * time_limit)
            tn, te = _twin_augment(best[0], best[1], d, rng, short)
            consider(tn, te)
            n2, e2 = _grow(tn, te, d, D,
                           min(deadline, time.monotonic() + 0.02 * time_limit),
                           rng, 200, True)
            consider(n2, e2)
            continue
        if D >= 3 and r < 0.2:
            short = min(deadline, time.monotonic() + 0.05 * time_limit)
            n2, e2 = _grow(best[0], best[1], d, D, short, rng, 200, True)
            consider(n2, e2)
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
        if res is not None:
            consider(res[0], res[1])

    # NEW phase (D >= 4): large-neighbourhood search with slot reuse,
    # started from the current best graph.
    if D >= 4:
        lns_end = start + 0.80 * time_limit
        try:
            _lns_search(best[0], best[1], d, D, lns_end,
                        random.Random(seed * 104729 + 17), consider)
        except Exception:
            pass

    # Repair phase (D >= 4): repeatedly insert one vertex into the current best
    # graph and anneal with degree-conserving moves until diameter D holds.
    if D >= 4:
        rend = start + 0.86 * time_limit
        fails = 0
        while time.monotonic() < rend - 0.5 and fails < 6:
            now = time.monotonic()
            slice_end = min(rend, now + max(3.0, 0.3 * (rend - now)))
            res = _repair_anneal(best[0], best[1], d, D, slice_end, rng)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                consider(res[0], res[1])
                fails = 0
            else:
                fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
