import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane and Araujo-Pardo-Lopez for small D.
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

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
# NEW: signed 2-lift (Bilu-Linial style doubling) of a bipartite base graph.
#
# Each base vertex u gives two copies 2u and 2u+1. Base edge (u, v) with sign s
# becomes (2u+c, 2v+(c xor s)) for c in {0,1}. Degrees are preserved and the
# lift of a bipartite graph is bipartite (every cycle lifts to a closed walk
# of the same or double length, which is even). Signs are annealed so that the
# lift has diameter <= D; if it cannot, the lift is repaired by deleting far
# vertices, which can still produce an order above the current best.
# ----------------------------------------------------------------------------

def _lift_edges(n, base, signs):
    E = []
    for (u, v), s in zip(base, signs):
        for c in (0, 1):
            E.append((2 * u + c, 2 * v + (c ^ s)))
    return 2 * n, E


def _double_cost(N, E, D):
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    ball = _balls_radius(N, adj, D)
    return sum(N - x.bit_count() for x in ball)


def _double_search(n, base, D, deadline, rng):
    """Anneal edge signs of a 2-lift. Returns (N, E, cost) of the final lift."""
    m = len(base)
    signs = [rng.randrange(2) for _ in range(m)]
    N, E = _lift_edges(n, base, signs)
    c = _double_cost(N, E, D)
    T = 2.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        signs[i] ^= 1
        N2, E2 = _lift_edges(n, base, signs)
        c2 = _double_cost(N2, E2, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c, N, E = c2, N2, E2
        else:
            signs[i] ^= 1
        T = max(0.05, T * 0.995)
    return N, E, c


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over non-abelian groups (cost 0 iff valid).
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _mul_table(order, mul):
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x, :] = [mul(x, y) for y in range(order)]
    return M


def _group_specs(lo, hi, cap=60):
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, ("aff", p)))
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            o = m * k
            if o < lo or o > hi:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 and r != 1:
                    specs.append((o, ("sd", m, k, r)))
                    break
    specs.sort(key=lambda t: (t[0], 0 if t[1][0] == "aff" else 1))
    return specs[:cap]


def _make_group(spec):
    if spec[0] == "aff":
        p = spec[1]
        order = p * (p - 1)
        return order, _mul_table(order, _affine_mul(p))
    _, m, k, r = spec
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, _mul_table(order, mul)


def _identity_ok(M):
    G = M.shape[0]
    ar = np.arange(G)
    return bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))


def _bc_adj(M, inv, S, G):
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    return np.vstack([G + M[:, Sa], M[:, iS]])


def _bc_cost(adj, G, D):
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _search_group(M, G, d, D, deadline, rng, iters=1500):
    inv = np.argmax(M == 0, axis=1)
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
        T = 2.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            T = max(0.05, T * 0.997)
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T2 = list(S)
            T2[i] = x
            c2 = _bc_cost(_bc_adj(M, inv, T2, G), G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = T2, c2
        if c == 0:
            return S
    return None


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _bicayley_phase(d, D, lo, deadline, rng, accept):
    best_G = lo - 1
    hi = int(1.5 * lo) + 2
    rnd = 0
    while time.monotonic() < deadline:
        budget = (1.0, 2.5, 5.0, 10.0)[min(rnd, 3)]
        rnd += 1
        specs = _group_specs(max(best_G + 1, lo), hi, cap=60)
        if not specs:
            break
        for o, spec in specs:
            if time.monotonic() >= deadline:
                return
            if o <= best_G:
                continue
            try:
                G, M = _make_group(spec)
            except Exception:
                continue
            if not _identity_ok(M):
                continue
            sub = min(deadline, time.monotonic() + budget)
            S = _search_group(M, G, d, D, sub, rng)
            if S is None:
                continue
            best_G = max(best_G, G)
            n, e = _bc_edges(M, S, G)
            accept(n, e)


# ----------------------------------------------------------------------------
# Non-cyclic voltage lifts over semidirect products, annealed.
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


def _focused_move(k, G, D, darts, perms, mul, rng, cost, limit, samples):
    idx = rng.randrange(len(darts))
    old_s = darts[idx][2]
    old_perm = perms[idx]
    best_c, best_s = None, None
    for _ in range(samples):
        s = rng.randrange(G)
        if s == old_s:
            continue
        darts[idx][2] = s
        perms[idx] = _right_perm(mul, G, s)
        c = _cost(k, G, D, darts, perms, limit if best_c is None else best_c)
        if best_c is None or c < best_c:
            best_c, best_s = c, s
    darts[idx][2] = old_s
    perms[idx] = old_perm
    if best_c is None or best_c > limit:
        return cost
    darts[idx][2] = best_s
    perms[idx] = _right_perm(mul, G, best_s)
    return best_c


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
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        r = rng.random()
        if r < 0.25:
            cost = _focused_move(k, G, D, darts, perms, mul, rng, cost, limit, 4)
        elif r < 0.7 or k == 1:
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
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    best_n = best[0]
    pool = []  # valid graphs kept as bases for signed 2-lifts

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            pool.append(pg)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
            pool.append(ar)

    # Bi-Cayley family for D >= 5 (smaller share of the budget).
    if D >= 5 and d >= 3:
        moore_half = lib.moore_bound(d, D) // 2
        lo = max(2 * d, best_n // 2 + 1, int(0.4 * moore_half))

        def accept_bc(n, e):
            if consider(n, e):
                pool.append((n, e))

        fam_rng = random.Random(seed * 1000003 + d * 131 + D)
        _bicayley_phase(d, D, lo, start + 0.4 * time_limit, fam_rng, accept_bc)

    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
    elite = {}
    while time.monotonic() < deadline:
        # NEW: signed 2-lift of a mid-sized valid base (order ~ best/2 .. 0.75 best),
        # so that the doubled graph lands above the current best order.
        if D >= 5 and rng.random() < 0.3:
            cands = [g for g in pool if best_n / 2 < g[0] <= 0.75 * best_n]
            base_g = rng.choice(cands) if cands else best
            N, E, c = _double_search(base_g[0], base_g[1], D,
                                     min(deadline, time.monotonic() + 6.0), rng)
            if c == 0:
                if consider(N, E):
                    pool.append((N, E))
            elif c <= 200 and time.monotonic() < deadline:
                rep = _repair(N, E, D, min(deadline, time.monotonic() + 3.0), rng)
                if rep is not None:
                    n3, e3 = rep
                    e3 = _saturate_edges(n3, e3, d, rng)
                    if consider(n3, e3):
                        pool.append((n3, e3))
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
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
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, deadline, iters,
                                    start_darts, T0)
        if res is not None:
            if consider(res[0], res[1]):
                pool.append(res)
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
