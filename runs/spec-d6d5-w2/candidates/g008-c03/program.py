import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small-D baseline families.
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


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
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


# ----------------------------------------------------------------------------
# Graph utilities.
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


def _ball_layers(n, adj, D):
    """layers[i][v] = bitmask of vertices within distance i of v, for i = 0..D."""
    layers = [[1 << v for v in range(n)]]
    for _ in range(D):
        prev = layers[-1]
        new = []
        for v in range(n):
            x = prev[v]
            for u in adj[v]:
                x |= prev[u]
            new.append(x)
        layers.append(new)
    return layers


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


def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


# ----------------------------------------------------------------------------
# NEW helper: diameter-aware greedy saturation.
#
# Adding an edge never increases any distance, so saturation keeps a valid
# graph valid. For a candidate edge a-b (a on side 0, b on side 1) we count
# the currently-far pairs (x, y) that the new edge brings within distance D:
#     d(x, a) + 1 + d(b, y) <= D   (and the symmetric orientation).
# The greedy step adds the candidate with the largest such gain, which spends
# the spare degree where it helps the diameter most, instead of at random.
# ----------------------------------------------------------------------------

def _pair_gain(a, b, layers, D):
    """Number of far pairs (ordered by side) that edge a-b brings within distance D."""
    full = layers[D]
    gain = 0
    for p, q in ((a, b), (b, a)):
        for i in range(D):
            if i == 0:
                layer = 1 << p
            else:
                layer = layers[i][p] & ~layers[i - 1][p]
            target = layers[D - 1 - i][q]
            m = layer
            while m:
                low = m & -m
                x = low.bit_length() - 1
                m ^= low
                gain += (target & ~full[x]).bit_count()
    return gain


def _diam_saturate(n, edges, d, D, deadline, rng, max_cand=60):
    """Greedily add opposite-side edges with spare degree, choosing by diameter gain.

    Only adds edges, so a valid input stays valid (degree stays <= d, bipartite kept).
    """
    edges = list(edges)
    adj = [[] for _ in range(n)]
    E = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        E.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        if not left or not right:
            break
        pool = set()
        for _ in range(4 * max_cand):
            if len(pool) >= max_cand:
                break
            a = rng.choice(left)
            b = rng.choice(right)
            if (min(a, b), max(a, b)) in E:
                continue
            pool.add((a, b))
        if not pool:
            break
        layers = _ball_layers(n, adj, D)
        best, bg = None, -1
        for a, b in pool:
            g = _pair_gain(a, b, layers, D)
            if g > bg:
                bg, best = g, (a, b)
        a, b = best
        edges.append((a, b))
        E.add((min(a, b), max(a, b)))
        adj[a].append(b)
        adj[b].append(a)
        deg[a] += 1
        deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

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
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Each layer L is a permutation of the k B-vertices, so every vertex has degree d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


def _sample_group(G, rng, k2_choices=None):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns ((n, edges) or None, darts, cost).
    """
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


def _lift_repair(D, k, G, mul, darts, deadline, rng):
    """Build the full lift from darts and repair it by vertex deletion. Returns (n, edges) or None."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    return _repair(N, E, D, deadline, rng)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= lib.moore_bound(d, D):
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        if best_n >= lib.moore_bound(d, D):
            return best

    # Main search: annealed bi-Cayley lifts, near-miss repair, and
    # diameter-aware saturation of the repaired graphs.
    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
    haar_m, haar_miss = d + 1, 0
    elite = {}  # (k, order) -> (cost, darts, mul) of the best failed state so far
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break

        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
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
            consider(res[0], res[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        # Near miss: delete far-off vertices, then spend the freed degree
        # with diameter-aware saturation (new contribution).
        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(D, k, order, mul_use, darts_out, rep_deadline, rng)
            if out is not None:
                n_r, e_r = out
                consider(n_r, e_r)
                sat_deadline = min(deadline, time.monotonic() + 3.0)
                e_s = _diam_saturate(n_r, e_r, d, D, sat_deadline, rng)
                consider(n_r, e_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
