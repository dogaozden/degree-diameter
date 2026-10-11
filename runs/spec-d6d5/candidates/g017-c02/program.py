import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane and generalized quadrangle incidence graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q): diameter 4, degree q + 1. Points 0..P-1, lines P..2P-1."""
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
# Generic graph helpers.
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


def _ball_masks(n, adj, D):
    balls = [[1 << v for v in range(n)]]
    for _ in range(D):
        prev = balls[-1]
        cur = []
        for v in range(n):
            x = prev[v]
            for u in adj[v]:
                x |= prev[u]
            cur.append(x)
        balls.append(cur)
    return balls


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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1."""
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
    """Join deficient opposite-side vertices. Only adds edges, so diameter never increases."""
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


def _edge_gain(balls, a, b, D):
    g = 0
    for s in range(D):
        g += balls[s][a].bit_count() * balls[D - 1 - s][b].bit_count()
    return g


def _augment(n, edges, d, D, deadline, rng, samples=600, batch=8):
    """Add cross-side edges between deficient vertices, ranked by estimated gain."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    full = (1 << n) - 1

    while time.monotonic() < deadline:
        balls = _ball_masks(n, adj, D)
        if all(b == full for b in balls[D]):
            break
        left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        if not left or not right:
            break
        scored = []
        for _ in range(samples):
            a = rng.choice(left)
            b = rng.choice(right)
            if (min(a, b), max(a, b)) in existing:
                continue
            scored.append((_edge_gain(balls, a, b, D), a, b))
        if not scored:
            break
        scored.sort(reverse=True)
        added = 0
        for _, a, b in scored:
            if added >= batch:
                break
            key = (min(a, b), max(a, b))
            if deg[a] >= d or deg[b] >= d or key in existing:
                continue
            existing.add(key)
            edges.append((a, b))
            adj[a].append(b)
            adj[b].append(a)
            deg[a] += 1
            deg[b] += 1
            added += 1
        if added == 0:
            break
    return edges


def _grow(n, edges, d, D, deadline, rng):
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY: 6-regular bipartite graphs made from k disjoint copies of W(d-2)
# (degree d-1, diameter 4) plus a perfect point-to-line matching across all
# copies. Every copy is internally diameter-4, so only cross pairs need the
# matching to help. Annealing swaps matched lines to bring every pair within 5.
# ----------------------------------------------------------------------------

def _multi_copy_setup(q, k):
    B, base_edges = _gq_w(q)
    P0 = B // 2
    N = k * B
    base_adj = [[] for _ in range(N)]
    base_all = []
    for c in range(k):
        off = c * B
        for u, v in base_edges:
            a, b = off + u, off + v
            base_all.append((a, b))
            base_adj[a].append(b)
            base_adj[b].append(a)
    baseset = [set(x) for x in base_adj]
    pts = [c * B + v for c in range(k) for v in range(P0)]
    lns = [c * B + v for c in range(k) for v in range(P0, B)]
    return B, N, base_adj, baseset, base_all, pts, lns


def _init_matching(pts, lns, baseset, rng):
    """Random bijection points -> lines avoiding base edges; None if repair of conflicts fails."""
    M = len(pts)
    pm = lns[:]
    rng.shuffle(pm)
    for _ in range(2000):
        bad = [i for i in range(M) if pm[i] in baseset[pts[i]]]
        if not bad:
            return pm
        i = rng.choice(bad)
        j = rng.randrange(M)
        pm[i], pm[j] = pm[j], pm[i]
    return None


def _matching_cost(N, base_adj, mate, D):
    """Ordered pairs (x, y) with dist(x, y) > D."""
    adj = [base_adj[v] + [mate[v]] for v in range(N)]
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N - b.bit_count() for b in ball)


def _matching_anneal(N, base_adj, baseset, pts, pm, D, rng, deadline):
    """Metropolis search over pairwise swaps of matched lines. Returns (best_cost, best_pm)."""
    M = len(pts)
    mate = [-1] * N
    for i in range(M):
        mate[pts[i]] = pm[i]
        mate[pm[i]] = pts[i]
    cur = _matching_cost(N, base_adj, mate, D)
    best, best_pm = cur, pm[:]
    T = 20.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        p1, p2 = pts[i], pts[j]
        L1, L2 = pm[i], pm[j]
        if L2 in baseset[p1] or L1 in baseset[p2]:
            continue
        mate[p1] = L2
        mate[L2] = p1
        mate[p2] = L1
        mate[L1] = p2
        c2 = _matching_cost(N, base_adj, mate, D)
        T = max(0.5, T * 0.999)
        if c2 <= cur - T * math.log(1.0 - rng.random()):
            cur = c2
            pm[i], pm[j] = L2, L1
            if cur < best:
                best, best_pm = cur, pm[:]
        else:
            mate[p1] = L1
            mate[L1] = p1
            mate[p2] = L2
            mate[L2] = p2
    return best, best_pm


def _multi_copy_run(d, D, k, deadline, hard, rng, consider):
    q = d - 2
    if time.monotonic() >= deadline - 1.0:
        return
    B, N, base_adj, baseset, base_all, pts, lns = _multi_copy_setup(q, k)
    pm = _init_matching(pts, lns, baseset, rng)
    if pm is None:
        return
    cost, best_pm = _matching_anneal(N, base_adj, baseset, pts, pm, D, rng, deadline)
    E = list(base_all)
    E.extend(zip(pts, best_pm))
    if cost == 0:
        consider(N, E)
        return
    # Near miss: delete far-off vertices, then add edges into the freed degree.
    rep = _repair(N, E, D, min(hard, time.monotonic() + 5.0), rng)
    if rep is not None:
        n2, e2 = rep
        consider(n2, _saturate_edges(n2, e2, d, rng))


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (parent family).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng, k2_choices=None):
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
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
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _augment(n, e, d, D, deadline, rng)
    e = _saturate_edges(n, e, d, rng)
    return n, e


def _lift_loop(d, D, rng, deadline, consider, res):
    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
    elite = {}
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = res["n"] // (2 * k)
        lo = max(2, base + 1)
        if k == 1 and D >= 5:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = None
        if k2_pool is not None and rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_darts, T0 = None, 1.0
        mul_use = mul
        if key in elite and rng.random() < 0.5:
            _, st, mul_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1500 if k == 1 else 400
        r, darts_out, c = _anneal(d, D, k, order, mul_use, rng, deadline, iters,
                                  start_darts, T0)
        if r is not None:
            consider(r[0], r[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])
                grow_deadline = min(deadline, time.monotonic() + 3.0)
                n3, e3 = _grow(out[0], out[1], d, D, grow_deadline, rng)
                consider(n3, e3)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    hard = start + 0.88 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    res = {"g": lib.haar_graph(d, range(d))}
    res["n"] = res["g"][0]

    def consider(n, e):
        if n > res["n"] and lib.is_valid(n, e, d, D):
            res["n"] = n
            res["g"] = (n, e)

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * T, rng)
                consider(n2, e2)

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * T, rng)
                consider(n2, e2)

        eligible = D >= 5 and d - 2 >= 2 and lib.is_prime_power(d - 2)
        if eligible:
            # New family first (k = 4 gives 680 vertices for d = 6), then lifts,
            # then a k = 5 attempt with the remaining budget.
            _multi_copy_run(d, D, 4, start + 0.6 * T, hard, rng, consider)
            _lift_loop(d, D, rng, start + 0.7 * T, consider, res)
            _multi_copy_run(d, D, 5, start + 0.8 * T, hard, rng, consider)
        else:
            _lift_loop(d, D, rng, start + 0.8 * T, consider, res)
    except Exception:
        pass

    n_out, e_out = res["g"]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, e_out
