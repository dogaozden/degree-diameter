import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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
    """Greedily join deficient opposite-side vertices in random order."""
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


# ----------------------------------------------------------------------------
# NEW ENGINE: cyclic bi-Cayley lifts searched with bitset BFS.
#
# k A-layers and k B-layers, each a copy of Z_m. There are d "darts" per
# A-layer, arranged in d permutations t, so every vertex has degree exactly d.
# Dart (i, j, s) joins A_i,g to B_j,g+s for all g.
# Shifts by Z_m are automorphisms, so distances need only be measured from one
# representative per layer. Each BFS level is computed for a whole layer at
# once as an m-bit integer, using cyclic rotations.
# ----------------------------------------------------------------------------

def _rot(x, s, m, full):
    """Map bit g of x to bit (g + s) mod m."""
    return ((x << s) | (x >> (m - s))) & full


def _cyc_cost(k, m, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    full = (1 << m) - 1
    L = 2 * k
    N = L * m
    ds = [(i, k + j, s, (m - s) % m) for i, j, s in darts]
    total = 0
    for src in range(L):
        vis = [0] * L
        fr = [0] * L
        vis[src] = 1
        fr[src] = 1
        reached = 1
        for _ in range(D):
            nf = [0] * L
            for a, b, s, ns in ds:
                x = fr[a]
                if x:
                    nf[b] |= _rot(x, s, m, full)
                y = fr[b]
                if y:
                    nf[a] |= _rot(y, ns, m, full)
            cnt = 0
            for t in range(L):
                x = nf[t] & ~vis[t] & full
                nf[t] = x
                if x:
                    vis[t] |= x
                    cnt += x.bit_count()
            if cnt == 0:
                break
            reached += cnt
            fr = nf
        total += N - reached
    return total


def _cyc_search(d, D, k, m, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _cyc_cost(k, m, D, darts)
    base = cost if cost < _BIG else 50
    T0 = max(1.0, 0.02 * base)
    T1 = 0.2
    decay = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T1, T * decay)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cyc_cost(k, m, D, darts)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            t = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = t * k + a, t * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cyc_cost(k, m, D, darts)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return [tuple(x) for x in darts]
    return None


def _cyc_edges(k, m, darts):
    """Expand a cyclic bi-Cayley description into (n, edges)."""
    E = set()
    for i, j, s in darts:
        for g in range(m):
            E.add((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, sorted(E)


# ----------------------------------------------------------------------------
# Secondary engine: annealed semidirect-product lifts (pure Python).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    search_end = start + 0.8 * budget
    end = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb = lib.haar_graph(d, range(d))
    best_n, best_e = fb[0], list(fb[1])

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * budget, rng)
            consider(n2, e2)

    if D >= 4:
        ks = [2, 2, 3, 3, 4, 5, 6] if D >= 5 else [2, 3, 4]
        while time.monotonic() < search_end:
            if rng.random() < 0.75:
                # Cyclic bitset engine, targeting an order just above the current best.
                k = rng.choice(ks)
                m = best_n // (2 * k) + 1 + rng.randrange(0, 2)
                iters = max(600, 6000 // k)
                darts = _cyc_search(d, D, k, m, rng, search_end, iters)
                if darts is not None:
                    n, e = _cyc_edges(k, m, darts)
                    consider(n, e)
                    gn, ge = _grow(n, e, d, D, search_end, rng)
                    consider(gn, ge)
            else:
                # Semidirect engine, as a secondary family.
                k = rng.choice([1, 1, 2, 2, 3])
                base = best_n // (2 * k)
                G = max(2, base + 1 + rng.randrange(0, 3))
                g = _sample_group(G, rng)
                if g is None:
                    continue
                order, mul = g
                res = _anneal(d, D, k, order, mul, rng, search_end, iters=1500)
                if res is not None:
                    consider(res[0], res[1])
                    gn, ge = _grow(res[0], res[1], d, D, search_end, rng)
                    consider(gn, ge)

    # Final growth pass on the best graph found, within the remaining budget.
    if D >= 3 and time.monotonic() < end:
        gn, ge = _grow(best_n, best_e, d, D, end, rng)
        consider(gn, ge)

    if not lib.is_valid(best_n, best_e, d, D):
        fb = lib.haar_graph(d, range(d))
        return fb[0], list(fb[1])
    return best_n, [tuple(e) for e in best_e]
