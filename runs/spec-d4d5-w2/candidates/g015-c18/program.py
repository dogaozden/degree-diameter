import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r (adj: lists or sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


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
        ball = _balls(n, adj, D - 1)
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
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
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
# NEW FAMILY: annealed random d-regular bipartite graphs.
#
# Start from a Haar circulant (A_i ~ B_{i+s}, s in 0..d-1) and apply random
# degree-preserving 2-switches on the bipartite edge set. The cost is the
# number of unordered vertex pairs at distance > D, computed with bitmasks.
# Random regular bipartite graphs have a surprisingly high chance of diameter
# D at this order, so this family can climb past voltage-lift orders.
# ----------------------------------------------------------------------------

def _bad_pairs_sets(n, adj, D):
    reach = _balls(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _regular_anneal(N, d, D, rng, slice_deadline):
    """Return a list of (a, b) bipartite edges (a, b in 0..N-1) with diameter <= D, or None."""
    n = 2 * N
    adj = [set() for _ in range(n)]
    E = []
    for i in range(N):
        for s in range(d):
            b = (i + s) % N
            E.append((i, b))
            adj[i].add(N + b)
            adj[N + b].add(i)
    M = len(E)

    def move(i, j, ni, nj):
        for a, b in (E[i], E[j]):
            adj[a].discard(N + b)
            adj[N + b].discard(a)
        for a, b in (ni, nj):
            adj[a].add(N + b)
            adj[N + b].add(a)
        E[i] = ni
        E[j] = nj

    def try_swap():
        i = rng.randrange(M)
        j = rng.randrange(M)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        if (N + b2) in adj[a1] or (N + b1) in adj[a2]:
            return None
        return i, j, (a1, b2), (a2, b1)

    # Mix without cost evaluation to scramble the circulant structure.
    for _ in range(4 * M):
        cand = try_swap()
        if cand is not None:
            move(cand[0], cand[1], cand[2], cand[3])

    cost = _bad_pairs_sets(n, adj, D)
    if cost == 0:
        return list(E)
    best_cost = cost
    best_E = list(E)

    T0, T1 = 2.0, 0.1
    t0 = time.monotonic()
    span = max(1e-3, slice_deadline - t0)
    while True:
        now = time.monotonic()
        if now >= slice_deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac
        cand = try_swap()
        if cand is None:
            continue
        i, j, ni, nj = cand
        oi, oj = E[i], E[j]
        move(i, j, ni, nj)
        c2 = _bad_pairs_sets(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
                if cost == 0:
                    return list(E)
        else:
            move(i, j, oi, oj)

    return list(best_E) if best_cost == 0 else None


def _regular_search(d, D, deadline, rng, lo_N, consider):
    """Climb N (per side): each success raises N by one; failures retry the same N."""
    N = max(lo_N, d + 1)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0 or 2 * N > 700:
            break
        slice_t = min(remaining, max(3.0, 0.5 * remaining))
        E = _regular_anneal(N, d, D, rng, now + slice_t)
        if E is not None:
            consider(2 * N, [(a, N + b) for a, b in E])
            N += 1


# ----------------------------------------------------------------------------
# Parent's bi-Cayley voltage-lift family (kept as a second candidate source).
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms):
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


def _vedges(k, G, darts, perms):
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
    cost = _vcost(k, G, D, darts, perms)

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
            c2 = _vcost(k, G, D, darts, perms)
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
            c2 = _vcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    main_deadline = start + 0.8 * time_limit

    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase A: random regular bipartite graphs with annealed 2-switches.
    # For D >= 5 this gets half the budget; otherwise the rest of the budget.
    if D >= 5:
        reg_deadline = start + 0.5 * time_limit
    else:
        reg_deadline = main_deadline
    lo_N = best_n // 2 + 1
    _regular_search(d, D, reg_deadline, rng, lo_N, consider)

    # Phase B (D >= 5): voltage lifts over semidirect products, then growth.
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        anneal_iters = 1500
        while time.monotonic() < main_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, main_deadline, anneal_iters)
            if res is not None:
                consider(res[0], res[1])
                gn, ge = _grow(res[0], res[1], d, D, main_deadline, rng)
                consider(gn, ge)

        gn, ge = _grow(best[0], best[1], d, D, start + 0.9 * time_limit, rng)
        consider(gn, ge)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
