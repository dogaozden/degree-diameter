import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: projective plane and generalized quadrangle W(q).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k, annealed (seed structure).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
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


def _cost_lift(k, G, D, darts, perms):
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
    return total


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_lift(k, G, D, darts, perms)

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
            c2 = _cost_lift(k, G, D, darts, perms)
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
            c2 = _cost_lift(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW family: degree-preserving swap annealing with vertex-pair insertion.
#
# Maintain a bipartite graph (side 0 = A, side 1 = B) with max degree d.
# Growth: add one A-vertex x and one B-vertex y, and take d edges (a_i, b_i)
# with distinct a_i and distinct b_i. Replace them by (x, b_i) and (a_i, y).
# Degrees of old vertices are unchanged and x, y get degree d.
# Then anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b), which preserve
# bipartiteness and degrees, minimising the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _adj_sets(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _orient(n, edges):
    """Return (color, E) where E lists each edge as (A-vertex, B-vertex)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    return color, E


def _bad_pairs_fast(n, adj, D):
    """Number of unordered pairs at distance greater than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow_once(n, color, E, d, rng):
    """Insert one A-vertex and one B-vertex by splicing d edges; returns new state or None."""
    m = len(E)
    if m < d:
        return None
    order = list(range(m))
    rng.shuffle(order)
    chosen = []
    ua, ub = set(), set()
    for t in order:
        a, b = E[t]
        if a in ua or b in ub:
            continue
        chosen.append(t)
        ua.add(a)
        ub.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    x, y = n, n + 1
    E2 = [E[t] for t in range(m) if t not in cs]
    for t in chosen:
        a, b = E[t]
        E2.append((x, b))
        E2.append((a, y))
    color2 = list(color) + [0, 1]
    adj2 = _adj_sets(n + 2, E2)
    return n + 2, color2, E2, adj2


def _swap_anneal(n, E, adj, D, deadline, rng, T0):
    """Anneal 2-switches in place. Returns final cost (0 means valid)."""
    eset = set(E)
    cost = _bad_pairs_fast(n, adj, D)
    m = len(E)
    if m < 2:
        return cost
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = T0 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in eset or (c, b) in eset:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        nc = _bad_pairs_fast(n, adj, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cost


def _saturate(n, color, E, adj, d, rng):
    """Greedily add edges between deficient opposite-side vertices (in place)."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(left)
    for a in left:
        if len(adj[a]) >= d:
            continue
        rng.shuffle(right)
        for b in right:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                E.append((a, b))


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 6.0)
    if budget < 1.0:
        budget = max(0.5, 0.5 * time_limit)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, list(fb_e)
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n <= best_n:
            return
        try:
            if lib.is_valid(n, e, d, D):
                best_n, best_e = n, list(e)
        except Exception:
            pass

    # Stage 1: structured bases.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if best_n >= moore:
        return best_n, best_e

    # Stage 2: voltage lifts over small semidirect products (seed family).
    stage2_end = start + 0.45 * budget
    ks = [1, 1, 2, 2, 3, 4]
    try:
        while time.monotonic() < stage2_end and best_n < moore:
            k = rng.choice(ks)
            G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, stage2_end, iters=1500)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if best_n >= moore:
        return best_n, best_e

    # Stage 3: new family. Grow the best valid graph by spliced vertex pairs,
    # then repair with degree-preserving swap annealing.
    try:
        color, E = _orient(best_n, best_e)
        adj = _adj_sets(best_n, E)
        base = (best_n, color, E, adj)
        attempt_len = 6.0
        while time.monotonic() < deadline and base[0] + 2 <= moore:
            cand = _grow_once(base[0], base[1], base[2], d, rng)
            if cand is None:
                break
            n2, col2, E2, adj2 = cand
            att_end = min(deadline, time.monotonic() + attempt_len)
            cost = _swap_anneal(n2, E2, adj2, D, att_end, rng, 1.0)
            if cost == 0:
                _saturate(n2, col2, E2, adj2, d, rng)
                consider(n2, E2)
                base = (n2, col2, E2, adj2)
    except Exception:
        pass

    try:
        if not lib.is_valid(best_n, best_e, d, D):
            return fb_n, list(fb_e)
    except Exception:
        return fb_n, list(fb_e)
    return best_n, best_e
