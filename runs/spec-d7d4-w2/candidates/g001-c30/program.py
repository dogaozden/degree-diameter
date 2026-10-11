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
        if not chosen:
            break
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
# Cover-based vertex extension and edge saturation (diameter-preserving).
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
    """Join deficient opposite-side vertices with leftover spare degree."""
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
# Bad-pair count.
# ----------------------------------------------------------------------------

def _bad_count(N, adj, D):
    balls = _balls_radius(N, adj, D)
    return sum(N - b.bit_count() for b in balls) // 2


# ----------------------------------------------------------------------------
# Insertion + double-edge-switch annealing repair.
# ----------------------------------------------------------------------------

def _swap(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b)."""
    adj[a].remove(b)
    adj[b].remove(a)
    adj[c].remove(e)
    adj[e].remove(c)
    adj[a].append(e)
    adj[e].append(a)
    adj[c].append(b)
    adj[b].append(c)


def _insert_repair(n, edges, d, D, rng, deadline, iters):
    if D < 2 or len(edges) < 2:
        return None
    adj = [[] for _ in range(n)]
    for u, w in edges:
        adj[u].append(w)
        adj[w].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    full = (1 << n) - 1
    ball = _balls_radius(n, adj, D - 1)

    order = [0, 1]
    rng.shuffle(order)
    chosen, c = None, None
    for cc in order:
        cands = [s for s in range(n) if color[s] == cc and deg[s] < d]
        if not cands:
            continue
        ch = _greedy_cover(cands, ball, full, d, rng, True)
        if ch is None:
            ch = rng.sample(cands, min(d, len(cands)))
        c, chosen = cc, ch
        break
    if chosen is None:
        return None

    v = n
    N = n + 1
    color.append(1 - c)
    adj.append([])
    for s in chosen:
        adj[s].append(v)
        adj[v].append(s)

    E = []
    for u, w in edges:
        E.append((u, w) if color[u] == 0 else (w, u))
    for s in chosen:
        E.append((s, v) if color[s] == 0 else (v, s))
    E = [list(x) for x in E]
    eset = {(min(a, b), max(a, b)) for a, b in E}

    cost = _bad_count(N, adj, D)
    it = 0
    while cost > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        T = 2.0 * (0.02 ** (it / iters))
        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        c2, e = E[j]
        if a == c2 or b == e:
            continue
        k1 = (min(a, e), max(a, e))
        k2 = (min(c2, b), max(c2, b))
        if k1 in eset or k2 in eset:
            continue
        _swap(adj, a, b, c2, e)
        new = _bad_count(N, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            eset.discard((min(a, b), max(a, b)))
            eset.discard((min(c2, e), max(c2, e)))
            eset.add(k1)
            eset.add(k2)
            E[i] = [a, e]
            E[j] = [c2, b]
        else:
            _swap(adj, a, e, c2, b)

    if cost != 0:
        return None
    return N, [(a, b) for a, b in E]


def _propose(N, adj, color, d, rng):
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


def _repair_anneal(n, edges, d, D, deadline, rng):
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
# Iterated local search: delete a vertex, repair, regrow.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _ils(n, edges, d, D, deadline, rng, holder):
    """holder[0] is the best verified (n, edges) so far; updated in place."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rn <= 0:
            continue
        if not lib.within_diameter(rn, re, D):
            re = _saturate_edges(rn, re, d, rng)
            if not lib.within_diameter(rn, re, D):
                continue
        rn, re = _fill(rn, re, d, D, rng, deadline)
        if rn >= cn:
            cn, ce = rn, re
            if rn > holder[0][0] and lib.is_valid(rn, re, d, D):
                holder[0] = (rn, re)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _pick(rng, weights):
    total = sum(w for _, w in weights)
    x = rng.random() * total
    for name, w in weights:
        x -= w
        if x < 0:
            return name
    return weights[-1][0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    state = {"best": lib.haar_graph(d, range(d))}
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    def best_n():
        return state["best"][0]

    # ---- Phase 0: structured bases ------------------------------------------
    if D == 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * T, rng, 200)
                consider(n2, e2)
        except Exception:
            pass
        try:
            for n_c, e_c in _arc_extensions(d, start + 0.35 * T,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)
        except Exception:
            pass

    if D >= 4 and best_n() < moore:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.30 * T
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= twin_deadline:
                break
            try:
                gq = _gq_w(q)
                consider(gq[0], gq[1])
                share = (twin_deadline - now) / (len(qs) - idx)
                tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
                consider(tn, te)
                n2, e2 = _grow(tn, te, d, D,
                               min(deadline, time.monotonic() + 0.05 * T),
                               rng, 300, False)
                consider(n2, e2)
            except Exception:
                pass

    # ---- Phase 1: operator search --------------------------------------------
    chunk = max(2.0, 0.08 * T)

    def step(name, until):
        now = time.monotonic()
        if name == 'ils':
            holder = [state["best"]]
            _ils(holder[0][0], holder[0][1], d, D, until, rng, holder)
            consider(holder[0][0], holder[0][1])
        elif name == 'ins':
            res = _insert_repair(best_n(), state["best"][1], d, D, rng,
                                 min(until, now + chunk), 4000)
            if res is not None:
                consider(res[0], res[1])
        elif name == 'rep':
            res = _repair_anneal(best_n(), state["best"][1], d, D,
                                 min(until, now + chunk), rng)
            if res is not None:
                consider(res[0], res[1])
        elif name == 'twin':
            tn, te = _twin_augment(best_n(), state["best"][1], d, rng,
                                   min(until, now + 0.5 * chunk))
            consider(tn, te)
            n2, e2 = _grow(tn, te, d, D, min(until, time.monotonic() + 0.5 * chunk),
                           rng, 200, True)
            consider(n2, e2)
        else:  # 'grow'
            n2, e2 = _grow(best_n(), state["best"][1], d, D,
                           min(until, now + chunk), rng, 200, True)
            consider(n2, e2)

    def weights():
        if D == 3:
            return [('ils', 0.45), ('ins', 0.2), ('rep', 0.2), ('grow', 0.15)]
        if D == 4:
            return [('ils', 0.4), ('ins', 0.25), ('rep', 0.2), ('twin', 0.1), ('grow', 0.05)]
        return [('ils', 0.5), ('rep', 0.3), ('grow', 0.2)]

    while time.monotonic() < deadline and best_n() < moore:
        name = _pick(rng, weights())
        sub = min(deadline, time.monotonic() + chunk)
        try:
            step(name, sub)
        except Exception:
            pass

    if not lib.is_valid(state["best"][0], state["best"][1], d, D):
        return lib.haar_graph(d, range(d))
    return state["best"]
