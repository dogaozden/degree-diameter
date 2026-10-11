import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Ceiling, orientation and distance helpers.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Moore-type ceiling for bipartite graphs (used only for early exit)."""
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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


def _orient(n, edges):
    """Return (n, edges) with every pair (a, b) such that a has colour 0 and b colour 1."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    return n, [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


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


def _unreached(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


# ----------------------------------------------------------------------------
# Safe seed: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: vertex-pair insertion by edge splitting.
#
# Pick d edges (x_i, y_i) with distinct x's and distinct y's. Replace each by
# (a, y_i) and add (x_i, b), where a is a new A-vertex and b a new B-vertex.
# Every old vertex keeps its degree, a and b get degree exactly d, and the
# graph stays bipartite. The result has two more vertices but may have
# diameter problems, which the swap annealer below repairs.
# ----------------------------------------------------------------------------

def _insert_pair(n, E, d, rng):
    """Return (n + 2, edges) after edge-splitting insertion, or None. E must be oriented."""
    if len(E) < d:
        return None
    idx = None
    for _ in range(200):
        cand = rng.sample(range(len(E)), d)
        xs = {E[i][0] for i in cand}
        ys = {E[i][1] for i in cand}
        if len(xs) == d and len(ys) == d:
            idx = cand
            break
    if idx is None:
        return None
    a, b = n, n + 1
    out = list(E)
    for i in idx:
        x, y = E[i]
        out[i] = (a, y)
        out.append((x, b))
    return n + 2, out


# ----------------------------------------------------------------------------
# NEW: degree-preserving double-edge-swap annealing on the exact count of
# unreached pairs. A swap of (a1,b1),(a2,b2) into (a1,b2),(a2,b1) keeps every
# degree and bipartiteness, so it repairs diameter without spoiling degrees.
# ----------------------------------------------------------------------------

def _relink(E, adj, S, i, na, nb):
    """Replace edge i by (na, nb), keeping adjacency lists and the edge set S in sync."""
    a, b = E[i]
    adj[a].remove(b)
    adj[b].remove(a)
    S.discard((a, b))
    E[i] = (na, nb)
    adj[na].append(nb)
    adj[nb].append(na)
    S.add((na, nb))


def _swap_anneal(n, E, D, deadline, rng, T0=2.0):
    """Anneal double-edge swaps to minimise unreached pairs. Returns (best_cost, best_edges)."""
    E = list(E)
    m = len(E)
    adj = [[] for _ in range(n)]
    S = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        S.add((a, b))
    cost = _unreached(n, adj, D)
    best_cost, best_E = cost, list(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0 and m >= 2:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.03, T0 * (1.0 - (now - t0) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _relink(E, adj, S, i, a1, b2)
        _relink(E, adj, S, j, a2, b1)
        c2 = _unreached(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost < best_cost:
                best_cost, best_E = cost, list(E)
        else:
            _relink(E, adj, S, j, a2, b2)
            _relink(E, adj, S, i, a1, b1)
    return best_cost, best_E


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over groups, annealed (secondary search that seeds
# the swap phase).
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
    """Number of (representative, vertex) pairs not reached within distance D."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters, T0=1.0):
    """Anneal voltages and B-assignments. Returns (edges_or_None, darts, cost)."""
    darts = _random_darts(d, k, G, rng)
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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until the diameter is at most D."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _ball_masks(cur_n, adj, D)[D]
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


def _edge_gain(balls, a, b, D):
    """Estimated number of pairs newly brought within distance D by adding edge a-b."""
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices (only adds edges)."""
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


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    """Build the full lift from darts, repair it, then augment and saturate."""
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
# Main entry point.
#
# Phase 1: projective-plane seed, then annealed group lifts (first half).
# Phase 2: repeatedly insert a vertex pair by edge splitting and repair the
#          diameter with degree-preserving swap annealing; keep successes.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback_n, fallback_e = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = [fallback_n, _orient(fallback_n, fallback_e)[1]]
    moore = _moore(d, D)

    def consider(n, E):
        if n > best[0] and lib.is_valid(n, E, d, D):
            best[0] = n
            best[1] = _orient(n, E)[1]

    def result():
        if lib.is_valid(best[0], best[1], d, D):
            return best[0], [(int(u), int(v)) for u, v in best[1]]
        return fallback_n, [(int(u), int(v)) for u, v in fallback_e]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if best[0] >= moore:
        return result()

    # Phase 1: annealed voltage lifts.
    mid = start + 0.5 * (deadline - start)
    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    while time.monotonic() < mid and best[0] < moore:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        lo = max(2, base + 1)
        hi = lo + (max(3, lo // 4) if k == 1 else max(3, lo // 8))
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool) if rng.random() < 0.8 else None
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res, darts, c = _anneal(d, D, k, order, mul, rng, mid, 1500 if k == 1 else 400)
        if res is not None:
            consider(res[0], res[1])
            continue
        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < mid:
            out = _lift_repair(d, D, k, order, mul, darts,
                               min(mid, time.monotonic() + 4.0), rng)
            if out is not None:
                consider(out[0], out[1])

    # Phase 2: edge-splitting growth with swap-annealing repair.
    while time.monotonic() < deadline and best[0] < moore:
        ins = _insert_pair(best[0], best[1], d, rng)
        if ins is None:
            break
        n2, E2 = ins
        now = time.monotonic()
        remaining = deadline - now
        dl = now + min(remaining, max(4.0, remaining / 3.0))
        cost, Eb = _swap_anneal(n2, E2, D, dl, rng)
        if cost == 0:
            consider(n2, Eb)

    return result()

