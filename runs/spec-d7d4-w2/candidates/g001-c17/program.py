import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: generalized quadrangle W(q) incidence graph (D = 4), projective
# planes (D = 3) come from lib.projective_plane_incidence.
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


# ----------------------------------------------------------------------------
# Parent pipeline (kept as a safety candidate): twin blow-up with spare-capacity
# packing, then cover-based vertex growth.
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
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


# ----------------------------------------------------------------------------
# NEW construction: d-regular bipartite graphs found by simulated annealing on
# the number of bad pairs, with vertex-pair growth.
#
# State: N vertices per side, a list E of d-regular bipartite edges (a, b) with
# a, b in 0..N-1. Start from a random circulant (shifts chosen at random, which is
# automatically simple and d-regular), then:
#   * move: 2-switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), preserving regularity;
#   * objective: number of unordered pairs at distance > D;
#   * when the objective is 0 the graph is verified and recorded, then grown by
#     one vertex on each side: d disjoint edges (a_k,b_k) are removed and replaced
#     by (a_k,N) and (N,b_k), with new vertices a_N and b_N each of degree d.
# Every record is re-verified with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def _bad_pairs_bip(N, E, D):
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
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


def _try_grow(N, E, d, rng):
    """Return (N+1, E', S') or None if no d disjoint edges can be found."""
    pick = None
    for _ in range(60):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        ua, ub = set(), set()
        cur = []
        for i in idx:
            a, b = E[i]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            cur.append(i)
            if len(cur) == d:
                break
        if len(cur) == d:
            pick = cur
            break
    if pick is None:
        return None
    pickset = set(pick)
    newE = [e for k, e in enumerate(E) if k not in pickset]
    for i in pick:
        a, b = E[i]
        newE.append((a, N))
        newE.append((N, b))
    return N + 1, newE, set(newE)


def _swap_pick(E, S, rng):
    m = len(E)
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a1, b1 = E[i]
    a2, b2 = E[j]
    if a1 == a2 or b1 == b2:
        return None
    if (a1, b2) in S or (a2, b1) in S:
        return None
    return i, j


def _apply_swap(E, S, i, j):
    a1, b1 = E[i]
    a2, b2 = E[j]
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal(d, D, rng, deadline, floor):
    """Return (n, edges) of the largest verified graph found above `floor`, or None."""
    N = max(d, lib.moore_bound(d, D) // 4)
    shifts = rng.sample(range(N), d)
    E = [(i, (i + s) % N) for s in shifts for i in range(N)]
    S = set(E)
    f = _bad_pairs_bip(N, E, D)
    T = 0.6
    found = None
    while time.monotonic() < deadline:
        if f == 0:
            n_out = 2 * N
            if n_out > floor:
                out = [(a, N + b) for a, b in E]
                if lib.is_valid(n_out, out, d, D):
                    found = (n_out, out)
                    floor = n_out
            g = _try_grow(N, E, d, rng)
            if g is None:
                for _ in range(30):
                    mv = _swap_pick(E, S, rng)
                    if mv is not None:
                        _apply_swap(E, S, *mv)
            else:
                N, E, S = g
            f = _bad_pairs_bip(N, E, D)
            continue
        mv = _swap_pick(E, S, rng)
        if mv is None:
            continue
        i, j = mv
        a1, b1 = E[i]
        a2, b2 = E[j]
        _apply_swap(E, S, i, j)
        f2 = _bad_pairs_bip(N, E, D)
        if f2 <= f or rng.random() < math.exp(-(f2 - f) / T):
            f = f2
        else:
            # undo the swap
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return found


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.75 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    base = None
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                base = lib.projective_plane_incidence(q)
                break
    else:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                base = _gq_w(q)
                break
    if base is not None:
        consider(base[0], base[1])
    if best[0] >= moore:
        return best

    # Parent pipeline as a safety candidate on a quarter of the budget.
    if base is not None:
        exp_deadline = start + 0.25 * budget
        if time.monotonic() < exp_deadline:
            n2, e2 = _expand(base[0], base[1], d, D, exp_deadline, rng)
            consider(n2, e2)

    # New construction: annealed regular bipartite graphs for the rest of the budget.
    if time.monotonic() < deadline:
        res = _anneal(d, D, rng, deadline, best[0])
        if res is not None:
            consider(res[0], res[1])

    return best
