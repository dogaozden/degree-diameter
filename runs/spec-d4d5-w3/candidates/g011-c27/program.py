import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic bases: projective plane (D=3) and generalized quadrangle W(q) (D=4).
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph utilities.
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


def _better(best, cand, d, D):
    """Return cand if it is strictly larger and valid, otherwise best."""
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return cand
    return best


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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within D-1 (keeps diameter D)."""
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
            for attempt in range(60):
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
    """Join deficient opposite-side vertices in random order, staying simple and bipartite."""
    edges = list(edges)
    adj = _adjacency(n, edges)
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


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(4):
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
# NEW: vertex-pair insertion and degree-preserving switch repair.
#
# Insertion: add a left vertex x and a right vertex y. Pick d right vertices r_i
# and, for each, one left neighbour l_i (all distinct). Replace edge (l_i, r_i)
# by (x, r_i) and add (l_i, y). Every old degree is preserved, x and y reach
# degree d, and bipartiteness is kept. This adds 2 vertices and d edges.
#
# Repair: simulated annealing over degree-preserving double-edge switches
# (a-b, c-e -> a-e, c-b), minimizing the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _insert_pair(n, edges, d, rng):
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    rights = [r for r in range(n) if color[r] == 1 and adj[r]]
    if len(rights) < d:
        return None
    chosen = rng.sample(rights, d)
    used = set()
    pairs = []
    for r in chosen:
        cands = [l for l in adj[r] if l not in used]
        if not cands:
            return None
        l = rng.choice(cands)
        used.add(l)
        pairs.append((l, r))
    S = set(edges)
    for l, r in pairs:
        S.discard((min(l, r), max(l, r)))
    x, y = n, n + 1
    for l, r in pairs:
        S.add((r, x))   # r < x
        S.add((l, y))   # l < y
    return n + 2, sorted(S)


def _switch(E, S, color, rng):
    """Degree-preserving double-edge swap, mutating E (list of normalized keys) and S (set)."""
    if len(E) < 2:
        return False
    i = rng.randrange(len(E))
    j = rng.randrange(len(E))
    if i == j:
        return False
    a, b = E[i]
    c, e = E[j]
    if color[a] == 1:
        a, b = b, a
    if color[c] == 1:
        c, e = e, c
    if a == c or b == e:
        return False
    k1 = (a, e) if a < e else (e, a)
    k2 = (c, b) if c < b else (b, c)
    if k1 in S or k2 in S:
        return False
    S.discard(E[i])
    S.discard(E[j])
    S.add(k1)
    S.add(k2)
    E[i] = k1
    E[j] = k2
    return True


def _repair_search(n, edges, d, D, deadline, rng, steps):
    """Repeatedly insert a vertex pair and anneal switches until diameter D again."""
    cur_n, cur_e = n, list(edges)
    fails = 0
    while time.monotonic() < deadline and cur_n + 2 <= lib.moore_bound(d, D):
        ins = _insert_pair(cur_n, cur_e, d, rng)
        if ins is None:
            break
        nn, ee = ins
        color = _bipartition(nn, _adjacency(nn, ee))
        E = list(ee)
        S = set(ee)
        cost = lib.bad_pairs(nn, E, D)
        T = 0.6
        for _ in range(steps):
            if cost == 0 or time.monotonic() > deadline:
                break
            E2 = list(E)
            S2 = set(S)
            if not _switch(E2, S2, color, rng):
                continue
            c2 = lib.bad_pairs(nn, E2, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                E, S, cost = E2, S2, c2
        if cost == 0:
            cur_n, cur_e = nn, sorted(E)
            fails = 0
        else:
            fails += 1
            if fails > 20:
                break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Annealed Z_m x| Z_k bi-Cayley voltage lifts (D >= 4 main family).
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


def _edges_of_lift(k, G, darts, perms):
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

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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
        return _edges_of_lift(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    # Structured bases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _better(best, pg, d, D)
            best = _better(best, _grow(pg[0], pg[1], d, D, start + 0.08 * time_limit, rng), d, D)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            best = _better(best, gq, d, D)
            best = _better(best, _grow(gq[0], gq[1], d, D, start + 0.15 * time_limit, rng), d, D)

    # Annealed group lifts, targeted just above the incumbent order.
    if D >= 4 and d >= 3:
        lift_deadline = start + 0.45 * time_limit
        ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        iters = 1500 if D >= 5 else 400
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters)
            if res is not None:
                best = _better(best, res, d, D)
                gn, ge = _grow(res[0], res[1], d, D, lift_deadline, rng)
                best = _better(best, (gn, ge), d, D)

    # NEW: repair-based growth from the incumbent using degree-preserving switches.
    if D >= 3 and d >= 3:
        rep_deadline = start + 0.85 * time_limit
        while time.monotonic() < rep_deadline:
            before = best[0]
            n2, e2 = _repair_search(best[0], best[1], d, D, rep_deadline, rng, 400)
            best = _better(best, (n2, e2), d, D)
            if best[0] <= before:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
