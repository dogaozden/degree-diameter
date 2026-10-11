import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small graph utilities.
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


def _adj(n, E):
    """Adjacency lists for an edge list."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _ball_bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitset BFS)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - x.bit_count() for x in ball) // 2


# ----------------------------------------------------------------------------
# NEW: double-edge-switch annealing on random regular bipartite graphs.
#
# Start from a d-regular bipartite graph on parts of size N (a Haar-type graph
# with d distinct shifts). A double-edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
# keeps every degree equal to d and keeps the graph bipartite. We anneal over
# switches to minimise the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _switch_anneal(N, d, D, rng, deadline):
    """Return an edge list of a d-regular bipartite graph on 2N vertices with diameter <= D, or None."""
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [(i, N + (i + s) % N) for i in range(N) for s in shifts]
    eset = set(E)
    m = len(E)
    cost = _ball_bad(n, _adj(n, E), D)
    T = 3.0
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        e1 = rng.randrange(m)
        e2 = rng.randrange(m)
        if e1 == e2:
            continue
        a1, b1 = E[e1]
        a2, b2 = E[e2]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        E[e1] = n1
        E[e2] = n2
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add(n1)
        eset.add(n2)
        c2 = _ball_bad(n, _adj(n, E), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            E[e1] = (a1, b1)
            E[e2] = (a2, b2)
            eset.discard(n1)
            eset.discard(n2)
            eset.add((a1, b1))
            eset.add((a2, b2))
        T = max(0.3, T * 0.9995)
    return E


# ----------------------------------------------------------------------------
# Greedy cover extension, saturation, and deletion repair.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _compact(n, edges, keep):
    """Relabel the kept vertices to 0..m-1 and keep only edges between them."""
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
# Bi-Cayley voltage lifts over semidirect products, annealed (parent family).
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
    """Permutation g -> mul(g, s) of the group."""
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
    """Copy of a dart assignment with `flips` random voltages re-rolled."""
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _focused_move(k, G, D, darts, perms, mul, rng, cost, limit, samples):
    """Pick one dart, try several voltages for it, keep the best if it passes the limit."""
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
    """Simulated annealing over voltages and per-layer B-assignments. Returns (edges_or_None, darts, cost)."""
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
    """Build the full lift from final darts, repair it, and saturate."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Projective-plane baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
                consider(n2, e2)
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

        if D >= 4:
            # Stage 1: annealed voltage lifts over semidirect products.
            lift_deadline = start + 0.3 * time_limit
            ks = [1, 1, 1, 2, 2, 3, 4]
            k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
            elite = {}
            while time.monotonic() < lift_deadline:
                k = rng.choice(ks)
                base = best_n // (2 * k)
                lo = max(2, base + 1)
                if k == 1:
                    hi = lo + max(3, lo // 4)
                else:
                    hi = lo + max(3, lo // 8)
                G = rng.randint(lo, hi)
                g = None
                if rng.random() < 0.8:
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
                res, darts_out, c = _anneal(d, D, k, order, mul_use, rng,
                                            lift_deadline, iters, start_darts, T0)
                if res is not None:
                    consider(res[0], res[1])
                    continue

                if key not in elite or c < elite[key][0]:
                    elite[key] = (c, darts_out, mul_use)

                if (c <= _REPAIR_MAX_COST and rng.random() < 0.35
                        and time.monotonic() < lift_deadline):
                    rep_deadline = min(lift_deadline, time.monotonic() + 4.0)
                    out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
                    if out is not None:
                        consider(out[0], out[1])
                        grow_deadline = min(lift_deadline, time.monotonic() + 3.0)
                        n3, e3 = _grow(out[0], out[1], d, D, grow_deadline, rng)
                        consider(n3, e3)

            # Stage 2 (NEW): double-edge-switch annealing on d-regular bipartite
            # graphs just above the current best order. Each success raises the target.
            while time.monotonic() < deadline:
                N = best_n // 2 + 1
                slice_end = min(deadline, time.monotonic() + 15.0)
                E = _switch_anneal(N, d, D, rng, slice_end)
                if E is not None:
                    consider(2 * N, E)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
