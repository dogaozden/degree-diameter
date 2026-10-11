import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
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


def _gq_bases(d, count):
    out = []
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            out.append(_gq_w(q))
            if len(out) == count:
                break
    return out


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

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


def _partial_cover(cands, ball, d, rng):
    """Greedy choice of up to d neighbours maximising newly covered vertices (may stop early)."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and pool:
        best = max(pool, key=lambda s: (ball[s] & ~covered).bit_count())
        if (ball[best] & ~covered) == 0:
            break
        chosen.append(best)
        pool.remove(best)
        covered |= ball[best]
    return chosen


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    attempts_max = 600 if D >= 4 else 200

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(12):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: bad-pair repair with bipartite 2-switches and edge additions.
# A vertex is added with partial cover; the graph is then repaired by
# 2-switches (which keep degrees and bipartiteness) and by adding edges
# between spare-degree vertices (which never increases bad pairs).
# ----------------------------------------------------------------------------

def _repair(n, edges, d, D, deadline, rng):
    E = [(u, v) for u, v in edges]
    S = {(min(u, v), max(u, v)) for u, v in E}
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    color = _bipartition(n, _adjacency(n, E))
    cur = lib.bad_pairs(n, E, D)

    while cur > 0 and time.monotonic() < deadline:
        added = False
        if rng.random() < 0.25:
            L = [v for v in range(n) if color[v] == 0 and deg[v] < d]
            R = [v for v in range(n) if color[v] == 1 and deg[v] < d]
            if L and R:
                a = rng.choice(L)
                b = rng.choice(R)
                k = (min(a, b), max(a, b))
                if k not in S:
                    E.append((a, b))
                    S.add(k)
                    deg[a] += 1
                    deg[b] += 1
                    cur = lib.bad_pairs(n, E, D)
                    added = True
        if added:
            continue

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if color[a] == 1:
            a, b = b, a
        if color[c] == 1:
            c, e = e, c
        if a == c or b == e:
            continue
        k1 = (min(a, e), max(a, e))
        k2 = (min(c, b), max(c, b))
        if k1 in S or k2 in S:
            continue
        old_i, old_j = E[i], E[j]
        ki = (min(old_i), max(old_i))
        kj = (min(old_j), max(old_j))
        E[i] = (a, e)
        E[j] = (c, b)
        S.discard(ki)
        S.discard(kj)
        S.add(k1)
        S.add(k2)
        new = lib.bad_pairs(n, E, D)
        if new <= cur or rng.random() < 0.01:
            cur = new
        else:
            E[i] = old_i
            E[j] = old_j
            S.discard(k1)
            S.discard(k2)
            S.add(ki)
            S.add(kj)
    return E if cur == 0 else None


def _repair_growth(d, D, deadline, rng, consider, st):
    while time.monotonic() < deadline:
        n, e = st["best"]
        adj = _adjacency(n, e)
        deg = [len(a) for a in adj]
        color = _bipartition(n, adj)
        ball = _balls_radius(n, adj, D - 1)
        c = rng.randrange(2)
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            break
        chosen = _partial_cover(cands, ball, d, rng)
        if not chosen:
            continue
        E = list(e) + [(s, n) for s in chosen]
        E = _saturate_edges(n + 1, E, d, rng)
        slice_end = min(deadline, time.monotonic() + max(1.0, (deadline - time.monotonic()) / 5))
        res = _repair(n + 1, E, d, D, slice_end, rng)
        if res is not None:
            consider(n + 1, res)


# ----------------------------------------------------------------------------
# Iterated local search with vertex excision and cover regrowth.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
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


def _ils(n, edges, d, D, deadline, rng, holder):
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        x = rng.randrange(cn)
        rn, re = _remove_vertex(cn, ce, x)
        if rng.random() < 0.2 and rn > 1:
            y = rng.randrange(rn)
            rn, re = _remove_vertex(rn, re, y)
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


def _final_ils(d, D, deadline, rng, st):
    if time.monotonic() >= deadline or st["best"][0] < 2:
        return
    holder = [st["best"]]
    _ils(st["best"][0], st["best"][1], d, D, deadline, rng, holder)
    if holder[0][0] > st["best"][0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
        st["best"] = holder[0]


# ----------------------------------------------------------------------------
# Scheduling.
# ----------------------------------------------------------------------------

def _run(d, D, seed, start, total, deadline, rng, consider, st):
    if D == 2:
        return
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return

    if D == 3:
        for b in _best_pg(d, 2):
            consider(b[0], b[1])
        _repair_growth(d, D, start + 0.5 * total, rng, consider, st)
        _final_ils(d, D, deadline, rng, st)
        return

    bases = _gq_bases(d, 2)
    for b in bases:
        consider(b[0], b[1])
    if not bases:
        return
    base = bases[seed % len(bases)]
    n, e = _grow(base[0], base[1], d, D, start + 0.2 * total, rng)
    consider(n, e)
    # New phase: repair-driven vertex addition from the current best.
    _repair_growth(d, D, start + 0.55 * total, rng, consider, st)
    _final_ils(d, D, deadline, rng, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    if st["best"][0] < lib._moore_bound(d, D):
        try:
            _run(d, D, seed, start, total, deadline, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
