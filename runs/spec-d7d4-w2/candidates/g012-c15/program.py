import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Graph utilities.
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


def _bad(n, adj, D):
    return sum(n - b.bit_count() for b in _balls_radius(n, adj, D)) // 2


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    """Alternate twin packing on both sides with cover growth, while the graph keeps growing."""
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


# ----------------------------------------------------------------------------
# NEW: Spare-slot insertion with degree-preserving annealing repair.
#
# Instead of only adding vertices whose neighbourhoods already cover the graph
# (which stalls once spare slots run out), we
#   1. attach a new vertex v to d opposite-side vertices chosen greedily for
#      radius-(D-1) coverage; a full neighbour gives up one edge, which frees
#      a slot on the far side,
#   2. saturate any remaining spare slots (this never increases bad pairs),
#   3. anneal the bad-pair count to zero with two moves:
#        A. bipartite 2-switch (degrees unchanged),
#        B. spare-slot move (an edge endpoint is redirected to a spare vertex).
# A successful insertion is kept only if lib.is_valid confirms it.
# ----------------------------------------------------------------------------

def _balls_sets(n, adj, r):
    """Radius-r ball bitmasks for a graph given as a list of neighbour sets."""
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


def _adj_bad(n, adj, D):
    """Number of unordered pairs at distance more than D (unreachable counts)."""
    return sum(n - b.bit_count() for b in _balls_sets(n, adj, D)) // 2


def _swap_edge(adj, E, i, new):
    """Replace edge index i (E[i]) by `new`, keeping adjacency sets and E in sync."""
    a, b = E[i]
    adj[a].discard(b)
    adj[b].discard(a)
    x, y = new
    adj[x].add(y)
    adj[y].add(x)
    E[i] = (x, y)


def _cover_insert(n, adj, color, d, D, rng):
    """Attach a new vertex to d opposite-side vertices chosen greedily by coverage."""
    ball = _balls_sets(n, adj, D - 1)
    c = rng.randrange(2)
    pool = [s for s in range(n) if color[s] == 1 - c]
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while len(chosen) < d and pool:
        best, bi = -1, 0
        for idx, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best:
                best, bi = g, idx
        s = pool.pop(bi)
        chosen.append(s)
        covered |= ball[s]
        if best == 0:
            break
    v = n
    adj.append(set())
    color.append(c)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(sorted(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return n + 1


def _saturate_sets(n, adj, color, d, rng):
    """Add edges between non-adjacent opposite-side vertices with spare slots (in place)."""
    spL = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    spR = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in spL for b in spR if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(n, adj, color, d, D, rng, deadline, cap):
    """Drive bad-pair count to zero by annealing; returns True on success."""
    E = []
    for a in range(n):
        for b in adj[a]:
            if a < b:
                E.append((a, b) if color[a] == 0 else (b, a))
    cur = _adj_bad(n, adj, D)
    steps = 0
    while cur > 0 and steps < cap and E and time.monotonic() < deadline:
        steps += 1
        T = 0.6 * (1 - steps / cap) + 0.04
        spares = [v for v in range(n) if len(adj[v]) < d]
        if spares and rng.random() < 0.5:
            # Move B: redirect one endpoint of a random edge to a spare vertex t.
            t = rng.choice(spares)
            i = rng.randrange(len(E))
            a, b = E[i]
            if color[t] == 1:
                if t in adj[a] or t == b:
                    continue
                new = (a, t)
            else:
                if t in adj[b] or t == a:
                    continue
                new = (t, b)
            old = E[i]
            _swap_edge(adj, E, i, new)
            nb = _adj_bad(n, adj, D)
            if nb <= cur or rng.random() < math.exp(-(nb - cur) / T):
                cur = nb
            else:
                _swap_edge(adj, E, i, old)
        else:
            # Move A: bipartite 2-switch, degrees preserved.
            if len(E) < 2:
                continue
            i, j = rng.randrange(len(E)), rng.randrange(len(E))
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            oi, oj = E[i], E[j]
            _swap_edge(adj, E, i, (a, e))
            _swap_edge(adj, E, j, (c, b))
            nb = _adj_bad(n, adj, D)
            if nb <= cur or rng.random() < math.exp(-(nb - cur) / T):
                cur = nb
            else:
                _swap_edge(adj, E, j, oj)
                _swap_edge(adj, E, i, oi)
    return cur == 0


def _insert_phase(n, edges, d, D, rng, deadline, consider):
    """Repeatedly insert one vertex with annealing repair until the deadline or repeated failure."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        snap = ([set(s) for s in adj], list(color), n)
        n2 = _cover_insert(n, adj, color, d, D, rng)
        _saturate_sets(n2, adj, color, d, rng)
        ok = _anneal(n2, adj, color, d, D, rng, deadline, 2500)
        e2 = [(a, b) for a in range(n2) for b in adj[a] if a < b] if ok else None
        if ok and lib.is_valid(n2, e2, d, D):
            n = n2
            consider(n, e2)
            fails = 0
        else:
            adj, color, n = snap[0], snap[1], snap[2]
            fails += 1


# ----------------------------------------------------------------------------
# Iterated local search: vertex excision, saturation repair, cover regrowth.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


def _add_one(n, edges, d, D, rng):
    """Add one vertex by a degree-respecting cover; return (n+1, edges) or None."""
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
    """Repeatedly add cover vertices while possible, then saturate spare slots."""
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


def _move(cn, ce, d, D, rng, deadline, targeted):
    """Excise one vertex, repair the diameter if cheaply possible, then refill."""
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
    """Iterated local search; holder[0] is the best verified (n, edges) so far."""
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    expand_deadline = start + 0.30 * T
    insert_deadline = start + 0.60 * T
    search_deadline = start + 0.85 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    # Calibration shortcut: already at the Moore bound, nothing to gain.
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

    # Expansion: twin packing and cover growth from the bases.
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

    # Phase 1.5 (new): spare-slot insertion with annealing repair.
    if best[0] >= lib.moore_bound(d, D):
        return best
    if bases and best[0] > 0 and time.monotonic() < insert_deadline:
        try:
            _insert_phase(best[0], best[1], d, D, rng, insert_deadline, consider)
        except Exception:
            pass

    # Phase 2: iterated local search on the best graph found.
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
