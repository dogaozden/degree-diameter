import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls(n, adj, r):
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


# ----------------------------------------------------------------------------
# Twin blow-up (from the parent): twin v copies the neighbourhood of v.
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    """Choose candidates so each resource u is used by at most cap[u] chosen candidates."""
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
    adj = _adj(n, edges)
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
# Cover-based vertex extension (diameter-preserving) and edge saturation.
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


def _extend_cover(n, edges, d, D, deadline, rng, restarts):
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        ball = _balls(N, adj, D - 1)
        added = False
        for c in (0, 1):
            cands = [s for s in range(N) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for att in range(restarts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if chosen:
                v = N
                adj.append([])
                deg.append(0)
                color.append(1 - c)
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
    return len(adj), edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, restarts=100):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    """Alternate twin packing on both sides with cover growth while the graph grows."""
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
# NEW: insertion with edge stealing + annealing repair on bad pairs.
#
# State is a bipartite graph kept as adjacency sets with max degree d.
# A "good" state has zero bad pairs (distance > D). When good:
#   1. saturate spare degree with edge additions (never hurts distances),
#   2. snapshot it,
#   3. insert a new vertex whose d neighbours are chosen by greedy radius-(D-1)
#      cover over the opposite side; full neighbours give up one random edge.
# The insertion usually leaves some bad pairs. Degree-preserving double-edge
# swaps (and spare-slot edge additions) are then annealed on the bad-pair count.
# If repair stalls, the snapshot is restored and a different insertion is tried.
# ----------------------------------------------------------------------------

def _balls_sets(n, adj, r):
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


def _bad_sets(n, adj, D):
    return sum(n - b.bit_count() for b in _balls_sets(n, adj, D)) // 2


def _insert_steal(n, adj, color, d, D, rng):
    c = rng.randrange(2)
    side = [s for s in range(n) if color[s] == 1 - c]
    if not side:
        return n
    ball = _balls_sets(n, adj, max(D - 1, 0))
    pool = list(side)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    for _ in range(min(d, len(pool))):
        best_g = -1
        best_i = 0
        for i, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g:
                best_g, best_i = g, i
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    v = n
    adj.append(set())
    color.append(c)
    for s in chosen:
        if len(adj[s]) >= d:
            w = rng.choice(tuple(adj[s]))
            adj[s].discard(w)
            adj[w].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return n + 1


def _saturate_sets(n, adj, color, d, rng):
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _random_move(n, adj, color, d, rng):
    """Either add an edge between spare-degree opposite vertices, or do a double-edge swap."""
    if rng.random() < 0.25:
        left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if left and right:
            for _ in range(20):
                a = rng.choice(left)
                b = rng.choice(right)
                if b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    return ('add', a, b)
        return None
    a = rng.randrange(n)
    if color[a] != 0 or not adj[a]:
        return None
    b = rng.choice(tuple(adj[a]))
    c = rng.randrange(n)
    if color[c] != 0 or c == a or not adj[c]:
        return None
    e = rng.choice(tuple(adj[c]))
    if e == b or e in adj[a] or b in adj[c]:
        return None
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)
    return ('swap', a, b, c, e)


def _undo(adj, mv):
    if mv[0] == 'add':
        _, a, b = mv
        adj[a].discard(b)
        adj[b].discard(a)
    else:
        _, a, b, c, e = mv
        adj[a].discard(e)
        adj[e].discard(a)
        adj[c].discard(b)
        adj[b].discard(c)
        adj[a].add(b)
        adj[b].add(a)
        adj[c].add(e)
        adj[e].add(c)


def _sa_step(n, adj, color, d, D, bad, T, rng):
    mv = _random_move(n, adj, color, d, rng)
    if mv is None:
        return bad
    nb = _bad_sets(n, adj, D)
    if nb <= bad or rng.random() < math.exp(-(nb - bad) / T):
        return nb
    _undo(adj, mv)
    return bad


def _anneal_grow(n, edges, d, D, deadline, rng, report, stall_limit=300, T=0.5):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(a) for a in adj])
    bad = _bad_sets(n, adj, D)
    snap = None
    stall = 0
    while time.monotonic() < deadline:
        if bad == 0:
            _saturate_sets(n, adj, color, d, rng)
            report(n, adj)
            snap = (n, [set(a) for a in adj], list(color))
            stall = 0
            n = _insert_steal(n, adj, color, d, D, rng)
            bad = _bad_sets(n, adj, D)
        else:
            bad = _sa_step(n, adj, color, d, D, bad, T, rng)
            stall += 1
            if stall > stall_limit and snap is not None:
                n = snap[0]
                adj = [set(a) for a in snap[1]]
                color = list(snap[2])
                bad = _bad_sets(n, adj, D)
                stall = 0


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.8 * T
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

    def report(n, adj):
        if n > best_n:
            consider(n, [(u, v) for u in range(n) for v in adj[u] if u < v])

    # ---- Structured bases ----------------------------------------------------
    bases = []
    try:
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    bases.append(lib.projective_plane_incidence(q))
                    break
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                bases.append(lib.araujo_lopez_graph(d - 2))
        elif D >= 4:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            for q in qs:
                bases.append(_gq_w(q))
    except Exception:
        pass

    for b in bases:
        consider(b[0], b[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    # ---- Expansion from bases (parent's twin/cover growth) -------------------
    expand_deadline = start + 0.25 * T
    rot = 0
    for _ in range(8):
        if not bases or time.monotonic() >= expand_deadline:
            break
        if rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        try:
            n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    # ---- Insertion + annealing repair from the best graph found so far -------
    if best_n < lib.moore_bound(d, D):
        try:
            _anneal_grow(best[0], best[1], d, D, deadline, rng, report)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
