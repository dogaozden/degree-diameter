import math
import random
import time

import itertools

import lib


# ----------------------------------------------------------------------------
# Projective-plane and arc-extension baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

def _adj(n, edges):
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


def _ball_masks(n, adj, D):
    """balls[t][v] = bitmask of vertices within distance t of v, for t = 0..D."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adj(n, edges)
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
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = set((min(u, v), max(u, v)) for u, v in edges)
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
    """Estimated number of pairs newly brought within distance D by adding edge a-b."""
    g = 0
    for s in range(D):
        g += balls[s][a].bit_count() * balls[D - 1 - s][b].bit_count()
    return g


def _augment(n, edges, d, D, deadline, rng, samples=600, batch=8):
    """Add cross-side edges between deficient vertices, ranked by estimated gain."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = set((min(u, v), max(u, v)) for u, v in edges)
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
        adj = _adj(cur_n, cur_e)
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
# NEW: side-respecting Z_2 double cover with annealed signs.
#
# Given a bipartite graph with sides A (colour 0) and B (colour 1), form two
# copies of every vertex, (v, 0) and (v, 1), and for each edge u-v with sign
# s in {0, 1} join (u, a) to (v, a XOR s) for a = 0, 1. Every degree is
# preserved, the order doubles, and the result stays bipartite with sides
# {(u, a): u in A} and {(v, b): v in B}. Diameter is the only constraint, so
# the signs are annealed against the number of pairs farther apart than D,
# computed with radius-D bitmask balls over the whole doubled graph.
# ----------------------------------------------------------------------------

def _side_edges(n, edges):
    """Orient every edge as (u, v) with u on side 0 of the bipartition."""
    color = _bipartition(n, _adj(n, edges))
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _signed_double_cost(n, E, sg, D):
    """Number of ordered (vertex, vertex) pairs at distance > D in the signed double cover."""
    N = 2 * n
    adj = [[] for _ in range(N)]
    for (u, v), s in zip(E, sg):
        for a in (0, 1):
            x = u + a * n
            y = v + (a ^ s) * n
            adj[x].append(y)
            adj[y].append(x)
    reach = [1 << x for x in range(N)]
    for _ in range(D):
        new = []
        for x in range(N):
            r = reach[x]
            for y in adj[x]:
                r |= reach[y]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _signed_double(n, E, D, deadline, rng, iters):
    """Anneal signs so the signed double cover has diameter <= D. Returns signs or None."""
    m = len(E)
    if m == 0:
        return None
    sg = [rng.randrange(2) for _ in range(m)]
    cost = _signed_double_cost(n, E, sg, D)
    T = 2.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        sg[i] ^= 1
        c2 = _signed_double_cost(n, E, sg, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / max(T, 1e-3)):
            cost = c2
        else:
            sg[i] ^= 1
        T = max(0.05, T * 0.995)
    return sg if cost == 0 else None


def _apply_double(n, E, sg):
    """Materialise the signed double cover; returns (2n, edges)."""
    out = []
    for (u, v), s in zip(E, sg):
        for a in (0, 1):
            out.append((u + a * n, v + (a ^ s) * n))
    return 2 * n, out


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
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
    """Pick one dart, try `samples` random voltages for it, keep the best if it passes the limit."""
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
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (edges_or_None, darts, cost).
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
    """Build the full lift from final darts, repair it, then augment and saturate."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _augment(n, e, d, D, deadline, rng)
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    moore = lib._moore_bound(d, D)

    # Phase A: projective-plane and arc-extension baselines.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * T, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.25 * T,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Phase B: annealed group voltage lifts with elite warm restarts and repair.
    if D >= 4 and best_n < moore:
        lift_deadline = start + 0.6 * T
        ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
        elite = {}
        while time.monotonic() < lift_deadline and best_n < moore:
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
            res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, lift_deadline,
                                        iters, start_darts, T0)
            if res is not None:
                consider(res[0], res[1])
                continue

            if key not in elite or c < elite[key][0]:
                elite[key] = (c, darts_out, mul_use)

            if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < lift_deadline:
                rep_deadline = min(lift_deadline, time.monotonic() + 4.0)
                out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
                if out is not None:
                    consider(out[0], out[1])
                    grow_deadline = min(lift_deadline, time.monotonic() + 3.0)
                    n3, e3 = _grow(out[0], out[1], d, D, grow_deadline, rng)
                    consider(n3, e3)

    # Phase C: side-respecting Z_2 double covers of the best graph, with annealed signs.
    if D >= 3 and best_n < moore:
        dbl_deadline = start + 0.85 * T
        cur_n, cur_e = best
        for _ in range(3):
            if time.monotonic() >= dbl_deadline or 2 * cur_n > moore:
                break
            E = _side_edges(cur_n, cur_e)
            sg = _signed_double(cur_n, E, D, dbl_deadline, rng, 4000)
            if sg is None:
                break
            nn, ee = _apply_double(cur_n, E, sg)
            if not consider(nn, ee):
                break
            cur_n, cur_e = nn, ee
            grow_deadline = min(dbl_deadline, time.monotonic() + 2.0)
            n4, e4 = _grow(nn, ee, d, D, grow_deadline, rng)
            consider(n4, e4)
            cur_n, cur_e = best

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
