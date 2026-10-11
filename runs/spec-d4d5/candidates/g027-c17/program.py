import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound (same formula as lib, used for early exit).
# ----------------------------------------------------------------------------

def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Base: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Stage 1: annealed bi-Cayley voltage lifts over semidirect products.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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


def _cost(k, G, D, darts, perms):
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Stage 2 (new, bold): grow a valid graph by two vertices (one per side),
# then repair by degree-preserving edge switches and deficiency-filling adds,
# minimising the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _colour_sets(n, adj):
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


def _bad_pairs_adj(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts)."""
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


def _connect(adj, a, b):
    adj[a].add(b)
    adj[b].add(a)


def _disconnect(adj, a, b):
    adj[a].discard(b)
    adj[b].discard(a)


def _attach_new(v, n, adj, color, d, rng):
    """Give new vertex v up to d neighbours on the opposite side; steal edges if needed."""
    opp = [u for u in range(n) if color[u] != color[v]]
    if not opp:
        return
    rng.shuffle(opp)
    for u in opp:
        if len(adj[v]) >= d:
            break
        if len(adj[u]) < d and u not in adj[v]:
            _connect(adj, v, u)
    tries = 0
    while len(adj[v]) < d and tries < 300:
        tries += 1
        u = rng.choice(opp)
        if u in adj[v] or not adj[u]:
            continue
        w = rng.choice(tuple(adj[u]))
        if w == v:
            continue
        _disconnect(adj, u, w)
        _connect(adj, v, u)


def _repair(n, adj, color, d, D, rng, att, T0=3.0, T1=0.15):
    """Anneal the bad-pair count to zero by switches and adds. Returns True on success."""
    cur = _bad_pairs_adj(n, adj, D)
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    t0 = time.monotonic()
    span = max(1e-3, att - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= att:
            break
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac

        if rng.random() < 0.8:
            a = rng.choice(A)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            c = rng.choice(A)
            if not adj[c]:
                continue
            e = rng.choice(tuple(adj[c]))
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            _disconnect(adj, a, b)
            _disconnect(adj, c, e)
            _connect(adj, a, e)
            _connect(adj, c, b)
            new = _bad_pairs_adj(n, adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                _disconnect(adj, a, e)
                _disconnect(adj, c, b)
                _connect(adj, a, b)
                _connect(adj, c, e)
        else:
            da = [x for x in A if len(adj[x]) < d]
            db = [y for y in B if len(adj[y]) < d]
            if not da or not db:
                continue
            a = rng.choice(da)
            b = rng.choice(db)
            if b in adj[a]:
                continue
            _connect(adj, a, b)
            cur = _bad_pairs_adj(n, adj, D)  # adding edges never hurts
    return cur == 0


def _grow_repair(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex per side and repair; returns the largest valid graph reached."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _colour_sets(n, adj)
    best = (n, list(edges))
    cur_n, cur_adj, cur_col = n, adj, color
    while True:
        now = time.monotonic()
        left = deadline - now
        if left <= 0.5:
            break
        budget = min(left, max(4.0, 0.3 * left))
        att = now + budget
        nn = cur_n + 2
        nadj = [set(s) for s in cur_adj] + [set(), set()]
        ncol = list(cur_col) + [0, 1]
        _attach_new(cur_n, nn, nadj, ncol, d, rng)
        _attach_new(cur_n + 1, nn, nadj, ncol, d, rng)
        if _repair(nn, nadj, ncol, d, D, rng, att):
            E = [(u, v) for u in range(nn) for v in nadj[u] if u < v]
            if lib.is_valid(nn, E, d, D):
                best = (nn, E)
                cur_n, cur_adj, cur_col = nn, nadj, ncol
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = _moore(d, D)
    if best[0] >= moore:
        return best  # calibration cases with a known optimum return instantly

    # Stage 1: annealed group lifts.
    stage1_deadline = start + 0.35 * time_limit
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
    else:
        ks = [1, 1, 2, 3]
        anneal_iters = 400
    while time.monotonic() < stage1_deadline:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, stage1_deadline, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])
        if best[0] >= moore:
            return best

    # Stage 2: grow-and-repair from the best graph found so far.
    if D >= 3 and best[0] < moore:
        n2, e2 = _grow_repair(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
