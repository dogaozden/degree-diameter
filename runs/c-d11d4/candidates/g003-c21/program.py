"""Bold variant for the D >= 4 targets: add-and-repair search.

Idea: start from the best valid graph (the generalized quadrangle W(q) plus cover and
twin growth, as in the parent), add one vertex with d neighbours, saturate spare degree,
and then repair the diameter violations with simulated annealing over degree-preserving
2-switches and spare-degree edge additions. Every move keeps max degree <= d and
bipartiteness. Edge additions and 2-switches can never leave the graph without a
valid fallback, because the best graph is only replaced after is_valid passes.

Untested note: this is a high-variance experiment. The gain may be small, and the
fixed-size repair is slow in Python. The parent pipeline still runs for the rest of the
budget, so the score should not drop below the parent's result.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and lines of the symplectic GQ.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Twin extension: a twin of x keeps all old distances, so diameter is preserved.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension (parent method).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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
    """Greedy set cover of `full` by at most d candidate vertices."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover vertices first, then saturate with remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
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
# Add-and-repair search (new family for D >= 4).
# Graph state: adj = list of sets, color = list of 0/1 sides.
# ----------------------------------------------------------------------------

def _struct(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj, _bipartition(n, adj)


def _flatten(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _bad_count(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(n, adj, color, d, rng):
    """Append one vertex with d neighbours on the opposite side. Returns new n, or None."""
    c = rng.randrange(2)
    side = 1 - c
    cand = [b for b in range(n) if color[b] == side and len(adj[b]) < d]
    full = [b for b in range(n) if color[b] == side and len(adj[b]) == d]
    rng.shuffle(cand)
    rng.shuffle(full)
    targets = cand[:d]
    need = d - len(targets)
    if need > len(full):
        return None
    for b in full[:need]:
        x = rng.choice(list(adj[b]))  # free one slot at b; x becomes deficient
        adj[b].discard(x)
        adj[x].discard(b)
        targets.append(b)
    v = n
    adj.append(set())
    color.append(c)
    for b in targets:
        adj[v].add(b)
        adj[b].add(v)
    return n + 1


def _saturate_struct(n, adj, color, d, rng):
    """Greedily join deficient opposite-side vertices."""
    L0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    L1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in L0 for b in L1 if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _apply(adj, ops):
    for op, u, v in ops:
        if op == '+':
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _invert(ops):
    return [('-' if op == '+' else '+', u, v) for op, u, v in reversed(ops)]


def _switch_move(adj, S0, rng):
    """Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b) with a,c on side 0."""
    a = rng.choice(S0)
    c = rng.choice(S0)
    if not adj[a] or not adj[c] or a == c:
        return None
    b = rng.choice(list(adj[a]))
    e = rng.choice(list(adj[c]))
    if b == e or e in adj[a] or b in adj[c]:
        return None
    return [('-', a, b), ('-', c, e), ('+', a, e), ('+', c, b)]


def _add_move(adj, color, d, n, rng):
    """Add an edge between two deficient opposite-side vertices."""
    D0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    D1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not D0 or not D1:
        return None
    for _ in range(20):
        a = rng.choice(D0)
        b = rng.choice(D1)
        if b not in adj[a]:
            return [('+', a, b)]
    return None


def _repair(n, adj, color, d, D, rng, deadline, max_steps):
    """Simulated annealing on bad-pair count. Returns the final cost."""
    S0 = [v for v in range(n) if color[v] == 0]
    cur = _bad_count(n, adj, D)
    T = 0.6
    for _ in range(max_steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        if rng.random() < 0.8:
            ops = _switch_move(adj, S0, rng)
        else:
            ops = _add_move(adj, color, d, n, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        new = _bad_count(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply(adj, _invert(ops))
    return cur


def _addrepair_phase(best_n, best_e, d, D, rng, sa_end):
    """Repeat: add a vertex to the current best, saturate, repair. Returns best (n, e)."""
    cur_n, cur_e = best_n, best_e
    while time.monotonic() < sa_end:
        adj, color = _struct(cur_n, cur_e)
        nn = _add_vertex(cur_n, adj, color, d, rng)
        if nn is None:
            break
        _saturate_struct(nn, adj, color, d, rng)
        budget_end = min(sa_end, time.monotonic() + 6.0)
        cost = _repair(nn, adj, color, d, D, rng, budget_end, 400)
        if cost == 0:
            e2 = _flatten(nn, adj)
            if lib.is_valid(nn, e2, d, D):
                cur_n, cur_e = nn, e2
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over non-cyclic groups (parent method).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
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


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m."""
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


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D >= 3: projective planes (small budget; W(q) is stronger for D >= 4).
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            pg_end = start + (0.4 if D == 3 else 0.1) * time_limit
            t0 = time.monotonic()
            span = max(0.0, pg_end - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) with growth restarts.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            base_n, base_e = gq[0], gq[1]
            stage_end = start + 0.3 * time_limit
            for restart in range(4):
                if time.monotonic() >= stage_end:
                    break
                if restart % 2 == 0:
                    tn, te = _twin_grow(base_n, base_e, d, rng, stage_end)
                    n4, e4 = _grow(tn, te, d, D, stage_end, rng)
                else:
                    gn, ge = _grow(base_n, base_e, d, D, stage_end, rng)
                    tn, te = _twin_grow(gn, ge, d, rng, stage_end)
                    n4, e4 = _grow(tn, te, d, D, stage_end, rng)
                consider(n4, e4)

        # New family: add-and-repair from the current best graph.
        sa_end = start + 0.7 * time_limit
        if best_n > 2:
            try:
                rn, re_ = _addrepair_phase(best_n, best[1], d, D, rng, sa_end)
                consider(rn, re_)
            except Exception:
                pass  # keep the valid best graph found so far

    # Main search (parent pipeline for the remaining budget).
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
