import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: projective plane and Araujo-Pardo-Lopez (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Shared graph utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _deficit(n, adj, D):
    """Per vertex: number of vertices at distance more than D (unreached pairs)."""
    ball = _balls_radius(n, adj, D)
    return [n - b.bit_count() for b in ball]


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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = _adj_list(n, edges)
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


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        bad = _deficit(cur_n, _adj_list(cur_n, cur_e), D)
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
# NEW: signed 2-lift annealing with lift-then-prune.
#
# A 2-lift of a bipartite graph H with max degree d has two copies of every
# vertex; each edge uv gets a sign s in {0,1}. s=0 joins u0-v0 and u1-v1,
# s=1 joins u0-v1 and u1-v0. The lift keeps degree d, stays simple and
# bipartite, and doubles the order. We anneal the signs to minimise the number
# of unreached pairs within distance D. If annealing gets stuck with few
# misses, we delete the far-off vertices (_repair) so the lift keeps most of
# its doubled order. This is a family the group-lift search does not reach.
# ----------------------------------------------------------------------------

def _signed_edges(base_n, base_edges, signs):
    E = []
    for (u, v), s in zip(base_edges, signs):
        if s:
            E.append((u, v + base_n))
            E.append((u + base_n, v))
        else:
            E.append((u, v))
            E.append((u + base_n, v + base_n))
    return 2 * base_n, E


def _lift2_anneal(base_n, base_edges, D, deadline, rng, max_iters):
    """Anneal the signs of a 2-lift. Returns (cost, N, E) of the best signing found."""
    m = len(base_edges)
    signs = [rng.randrange(2) for _ in range(m)]
    N, E = _signed_edges(base_n, base_edges, signs)
    cost = sum(_deficit(N, _adj_list(N, E), D))
    best_cost, best_signs = cost, signs[:]
    T = 2.0
    it = 0
    while cost > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(m)
        signs[i] ^= 1
        N, E = _signed_edges(base_n, base_edges, signs)
        c2 = sum(_deficit(N, _adj_list(N, E), D))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost, best_signs = cost, signs[:]
        else:
            signs[i] ^= 1
        T = max(0.2, T * 0.997)
    N, E = _signed_edges(base_n, base_edges, best_signs)
    return best_cost, N, E


def _lift_stage(d, D, best_n, best_e, deadline, rng, consider):
    """Lift the current best graph by a signed 2-lift, anneal it, then prune if needed."""
    if best_n > 900 or not best_e or time.monotonic() >= deadline:
        return
    budget = min(deadline, time.monotonic() + 12.0)
    bc, N, E = _lift2_anneal(best_n, best_e, D, budget, rng, 3000)
    if bc == 0:
        consider(N, E)
        return
    if bc <= 3 * N and time.monotonic() < deadline:
        rep = _repair(N, E, D, min(deadline, time.monotonic() + 5.0), rng)
        if rep is not None:
            n, e = rep
            consider(n, _saturate_edges(n, e, d, rng))


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
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
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    return n, _saturate_edges(n, e, d, rng)


def _bicayley_step(d, D, best_n, deadline, rng, elite, consider):
    k = rng.choice([1, 1, 1, 2, 2, 3, 4])
    base = best_n // (2 * k)
    lo = max(2, base + 1)
    hi = lo + max(3, lo // 4 if k == 1 else lo // 8)
    G = rng.randint(lo, hi)
    g = _sample_group(G, rng)
    if g is None:
        return
    order, mul = g
    key = (k, order)
    start, T0, mul_use = None, 1.0, mul
    if key in elite and rng.random() < 0.5:
        _, st, mul_use = elite[key]
        start = _perturb(st, order, rng, rng.randint(1, 3))
        T0 = 0.5
    iters = 1500 if k == 1 else 400
    res, darts, c = _anneal(d, D, k, order, mul_use, rng, deadline, iters, start, T0)
    if res is not None:
        consider(res[0], res[1])
        return
    if key not in elite or c < elite[key][0]:
        elite[key] = (c, darts, mul_use)
    if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
        out = _lift_repair(d, D, k, order, mul_use, darts,
                           min(deadline, time.monotonic() + 4.0), rng)
        if out is not None:
            consider(out[0], out[1])


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    elite = {}
    step = 0
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break
        step += 1
        if step % 2 == 0:
            _lift_stage(d, D, best_n, best[1],
                        min(deadline, time.monotonic() + 12.0), rng, consider)
        else:
            _bicayley_step(d, D, best_n,
                           min(deadline, time.monotonic() + 10.0),
                           rng, elite, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
