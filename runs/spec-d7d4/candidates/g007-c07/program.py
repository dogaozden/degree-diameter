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
# Twin augmentation by packing: a twin x' of x (same neighbourhood, opposite
# side) keeps bipartiteness and all distances. Each neighbour of x uses one
# unit of its spare degree, so twins are chosen by a packing search.
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
# NEW: incremental vertex insertion with degree-preserving annealing repair.
#
# State: a bipartite graph with max degree d (not necessarily valid yet).
# Each growth step adds one vertex v on a chosen side, joined to d opposite
# vertices. Opposite vertices that are already full give up one edge, which
# creates a deficit on the other side. Deficits are then filled greedily.
# Simulated annealing on the number of pairs at distance > D then repairs the
# graph using two moves:
#   * double-edge swap (a-b, c-e) -> (a-e, c-b): keeps every degree;
#   * endpoint move (a-b) -> (a-e), e a deficit vertex: moves a deficit.
# A success is a valid graph one vertex larger; a failure reverts the step.
# ----------------------------------------------------------------------------

def _bad_count(n, adjl, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjl[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _set_edge(adjl, u, v, on):
    if on:
        adjl[u].add(v)
        adjl[v].add(u)
    else:
        adjl[u].discard(v)
        adjl[v].discard(u)


def _fill(n, adjl, col, d, rng):
    """Greedily join deficient opposite-side vertices."""
    L = [v for v in range(n) if col[v] == 0 and len(adjl[v]) < d]
    R = [v for v in range(n) if col[v] == 1 and len(adjl[v]) < d]
    rng.shuffle(L)
    rng.shuffle(R)
    for a in L:
        for b in R:
            if len(adjl[a]) >= d:
                break
            if len(adjl[b]) < d and b not in adjl[a]:
                _set_edge(adjl, a, b, True)


def _add_vertex(n, adjl, col, d, c, rng):
    """Append one vertex on side c, joined to d opposite-side vertices. Returns new n."""
    v = n
    adjl.append(set())
    col.append(c)
    opp = [w for w in range(n) if col[w] == 1 - c]
    rng.shuffle(opp)
    chosen = [w for w in opp if len(adjl[w]) < d][:d]
    if len(chosen) < d:
        for w in opp:
            if len(chosen) >= d:
                break
            if w not in chosen:
                chosen.append(w)
    for w in chosen:
        if len(adjl[w]) >= d:
            x = rng.choice(tuple(adjl[w]))
            _set_edge(adjl, w, x, False)
        _set_edge(adjl, w, v, True)
    return n + 1


def _sa(n, adjl, col, d, D, deadline, rng, iters):
    """Anneal toward zero bad pairs. Returns True when the graph becomes valid."""
    side = [[v for v in range(n) if col[v] == s] for s in (0, 1)]
    cur = _bad_count(n, adjl, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.03 ** (it / iters))
        if rng.random() < 0.6:
            a = rng.choice(side[0])
            c = rng.choice(side[0])
            if a == c or not adjl[a] or not adjl[c]:
                continue
            b = rng.choice(tuple(adjl[a]))
            e = rng.choice(tuple(adjl[c]))
            if b == e or e in adjl[a] or b in adjl[c]:
                continue
            _set_edge(adjl, a, b, False)
            _set_edge(adjl, c, e, False)
            _set_edge(adjl, a, e, True)
            _set_edge(adjl, c, b, True)
            new = _bad_count(n, adjl, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _set_edge(adjl, a, e, False)
                _set_edge(adjl, c, b, False)
                _set_edge(adjl, a, b, True)
                _set_edge(adjl, c, e, True)
        else:
            s = rng.randrange(2)
            deficits = [w for w in side[1 - s] if len(adjl[w]) < d]
            if not deficits:
                continue
            e = rng.choice(deficits)
            a = rng.choice(side[s])
            if not adjl[a] or e in adjl[a]:
                continue
            b = rng.choice(tuple(adjl[a]))
            _set_edge(adjl, a, b, False)
            _set_edge(adjl, a, e, True)
            new = _bad_count(n, adjl, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                _set_edge(adjl, a, e, False)
                _set_edge(adjl, a, b, True)
    return cur == 0


def _sa_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex and repair by annealing; return the largest valid graph seen."""
    adjl = [set() for _ in range(n)]
    for u, v in edges:
        adjl[u].add(v)
        adjl[v].add(u)
    col = _bipartition(n, [list(s) for s in adjl])
    _fill(n, adjl, col, d, rng)
    best = (n, [(u, v) for u in range(n) for v in adjl[u] if u < v])
    if _bad_count(n, adjl, D) == 0:
        pass
    while time.monotonic() < deadline:
        snap = ([set(s) for s in adjl], col[:], n)
        c = rng.randrange(2)
        n = _add_vertex(n, adjl, col, d, c, rng)
        _fill(n, adjl, col, d, rng)
        budget = min(deadline, time.monotonic() + 4.0)
        ok = _sa(n, adjl, col, d, D, budget, rng, 1500)
        if ok:
            best = (n, [(u, v) for u in range(n) for v in adjl[u] if u < v])
        else:
            adjl, col, n = snap
    return best


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    cap = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng, 200)
            consider(n2, e2)

    if D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.35 * time_limit
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
                           min(deadline, time.monotonic() + 0.03 * time_limit),
                           rng, 300, False)
            consider(n2, e2)

    # Skip the search when the Moore bound is already reached (e.g. calibration).
    if best_n < cap and time.monotonic() < deadline:
        n2, e2 = _sa_grow(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
