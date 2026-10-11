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
# Shared helpers.
# ----------------------------------------------------------------------------

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


def _saturate_edges(n, edges, d, rng):
    """Add edges between deficient opposite-side vertices. Adding edges never increases distances."""
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


# ----------------------------------------------------------------------------
# Twin augmentation (diameter-preserving: a twin copies a vertex's neighbourhood).
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
# Insertion + degree-preserving switch repair (from the parent).
# ----------------------------------------------------------------------------

def _bad_count(N, adj, D):
    balls = _balls_radius(N, adj, D)
    return sum(N - b.bit_count() for b in balls) // 2


def _swap(adj, a, b, c, e):
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


# ----------------------------------------------------------------------------
# NEW MAIN IDEA: bi-regular voltage lifts over NON-CYCLIC abelian groups.
#
# The group is a product of cyclic groups of prime-power order, chosen at
# random (so Z_2^a, Z_3^b, Z_4 x Z_2 ..., not just Z_m). Base graph has k
# vertices per side; layer L is a perfect matching A_i -> B_{p_L(i)} with a
# voltage per dart. Simulated annealing over voltages and matchings drives the
# number of (vertex, representative) pairs at distance > D to zero.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _factor(n):
    f = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def _random_mods(G, rng):
    """Random decomposition of G into cyclic factors of prime-power order (product = G)."""
    mods = []
    for p, e in _factor(G).items():
        while e > 0:
            part = e if rng.random() < 0.5 else rng.randint(1, e)
            mods.append(p ** part)
            e -= part
    return mods


def _abelian(mods):
    """Return (order, mul) for the product of Z_m over mods, element index in mixed radix."""
    G = 1
    for m in mods:
        G *= m
    weights = []
    w = 1
    for m in mods:
        weights.append(w)
        w *= m
    digs = [[(x // weights[t]) % mods[t] for t in range(len(mods))] for x in range(G)]
    R = range(len(mods))

    def mul(x, y):
        dx = digs[x]
        dy = digs[y]
        s = 0
        for t in R:
            s += ((dx[t] + dy[t]) % mods[t]) * weights[t]
        return s

    return G, mul


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
        u = 1.0 - random_uniform(rng)
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


def random_uniform(rng):
    return rng.random()


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # ---- D >= 4 ----
    # Phase A: generalized quadrangle bases, twin-augmented and saturated.
    qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
    phase_a_end = start + 0.2 * time_limit
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= phase_a_end:
            break
        gq = _gq_w(q)
        consider(gq[0], gq[1])
        share = (phase_a_end - now) / (len(qs) - idx)
        tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
        consider(tn, te)
        sat = _saturate_edges(tn, te, d, rng)
        consider(tn, sat)
        sat2 = _saturate_edges(gq[0], gq[1], d, rng)
        consider(gq[0], sat2)

    # Phase B: non-cyclic abelian voltage lifts, with occasional insert-repair.
    while time.monotonic() < deadline:
        if D == 4 and rng.random() < 0.12:
            slice_end = min(deadline, time.monotonic() + 0.05 * time_limit)
            res = _insert_repair(best_n, best[1], d, D, rng, slice_end, 3000)
            if res is not None:
                consider(res[0], res[1])
            continue

        k = rng.choice([1, 2, 2, 3, 3, 4])
        base = max(1, best_n // (2 * k))
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        mods = _random_mods(G, rng)
        order, mul = _abelian(mods)
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=800)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
