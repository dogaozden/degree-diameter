import math
import random
import time

import lib


_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Primary new family: voltage lifts of the projective plane incidence graph
# PG(2, q), q = d - 1, over small groups of order G (cyclic or semidirect).
#
# The base graph has 2m vertices and is (q+1) = d regular. A lift over a group of
# order G has 2m*G vertices, keeps degree d, and is bipartite. Left translations
# are automorphisms, so checking the fibre of each base vertex suffices for the
# diameter. Voltages are annealed to minimise the number of unreached pairs.
# ----------------------------------------------------------------------------

def _group_options(G):
    """All (m, k, r) with semidirect_group(m, k, r) of order G (cyclic included)."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _lift_balls(base_n, G, base_edges, volt, R, D):
    """Bitmask of vertices within distance D for every lift vertex."""
    N = base_n * G
    adj = [[] for _ in range(N)]
    for (u, v), s in zip(base_edges, volt):
        Rs = R[s]
        ub, vb = u * G, v * G
        for x in range(G):
            a = ub + x
            b = vb + Rs[x]
            adj[a].append(b)
            adj[b].append(a)
    ball = [1 << i for i in range(N)]
    for _ in range(D):
        new = [0] * N
        for i in range(N):
            acc = ball[i]
            for j in adj[i]:
                acc |= ball[j]
            new[i] = acc
        ball = new
    return N, ball


def _lift_cost(base_n, G, base_edges, volt, R, D):
    """Total number of unreached (fibre representative, vertex) pairs; zero means diameter <= D."""
    N, ball = _lift_balls(base_n, G, base_edges, volt, R, D)
    return sum(N - ball[u * G].bit_count() for u in range(base_n))


def _lift_edges(base_n, G, base_edges, volt, R):
    E = set()
    for (u, v), s in zip(base_edges, volt):
        Rs = R[s]
        for x in range(G):
            a = u * G + x
            b = v * G + Rs[x]
            E.add((a, b) if a < b else (b, a))
    return base_n * G, sorted(E)


def _lift_anneal(base_n, G, base_edges, R, D, deadline, rng):
    """Anneal voltages on the base edges. Returns (voltages or None, cost)."""
    E = len(base_edges)
    volt = [rng.randrange(G) for _ in range(E)]
    cur = _lift_cost(base_n, G, base_edges, volt, R, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 3.0 * (0.01 ** frac)
        idx = rng.randrange(E)
        old = volt[idx]
        new = rng.randrange(G)
        if new == old:
            continue
        volt[idx] = new
        c = _lift_cost(base_n, G, base_edges, volt, R, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[idx] = old
    return (volt if cur == 0 else None), cur


def _pg_lift_search(d, D, q, deadline, rng, best_n):
    """Search lifts of PG(2, q) over small groups; returns the best valid (n, edges) found or None."""
    base_n, base_edges = lib.projective_plane_incidence(q)
    cap = lib._moore_bound(d, D)
    best = None
    while time.monotonic() < deadline:
        g_min = best_n // base_n + 1
        if base_n * g_min > cap:
            break
        G = rng.choice([g_min, g_min, g_min + 1, g_min + 2])
        if base_n * G > cap:
            G = g_min
        m_, k_, r_ = rng.choice(_group_options(G))
        order, mul, _ = lib.semidirect_group(m_, k_, r_)
        R = [[mul(x, s) for x in range(order)] for s in range(order)]
        slice_end = min(deadline, time.monotonic() + 15.0)
        volt, _ = _lift_anneal(base_n, order, base_edges, R, D, slice_end, rng)
        if volt is None:
            continue
        n, e = _lift_edges(base_n, order, base_edges, volt, R)
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
    return best


# ----------------------------------------------------------------------------
# Secondary family: bi-Cayley voltage lifts over semidirect products, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
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
    """Annealing over voltages and per-layer B-assignments. Returns (edges_or_None, darts, cost)."""
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


# ----------------------------------------------------------------------------
# Repair of near-miss lifts by vertex deletion, then saturation.
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    cap = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing to search for.
    if best_n >= cap:
        return best

    # New family: voltage lifts of PG(2, d-1), which is d-regular.
    q = d - 1
    if D >= 4 and q >= 2 and lib.is_prime_power(q):
        share = 0.6 if D == 5 else 0.3
        pg_deadline = start + share * 0.85 * time_limit
        res = _pg_lift_search(d, D, q, pg_deadline, rng, best_n)
        if res is not None:
            consider(res[0], res[1])

    if best_n >= cap:
        return best

    # Secondary family: annealed bi-Cayley lifts with elite restarts and repair.
    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    fallback_pool = [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    elite = {}
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        if k == 1 and D >= 5:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = None
        if rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng, fallback_pool)
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
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, deadline, iters,
                                    start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            if best_n >= cap:
                break
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
