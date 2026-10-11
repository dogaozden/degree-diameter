import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# (Same family as the parent; used to find the base graph.)
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8])
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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments (Metropolis via pre-drawn threshold)."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
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
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: edge-switch growth with annealed repair.
#
# Given a simple bipartite graph (every edge stored as (u, v) with u on side 0),
# add a new side-0 vertex a and a new side-1 vertex b by taking d-1 existing
# edges (x_t, y_t) with distinct x_t and distinct y_t, then rewiring:
#     remove (x_t, y_t);  add (x_t, b),  (a, y_t),  and  (a, b).
# Every old vertex keeps its degree, a and b get degree d, and the result is
# bipartite. The diameter is then repaired by double-edge swaps
# (u1,v1),(u2,v2) -> (u1,v2),(u2,v1), which keep all degrees and sides,
# minimising the number of vertex pairs at distance > D (simulated annealing).
# ----------------------------------------------------------------------------

def _adjacency(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _grow_once(n, E, d, D, rng, iters, deadline):
    """Try to add one (side-0, side-1) vertex pair with degree d and repair diameter by annealing."""
    r = d - 1
    m = len(E)
    if r < 1 or m < r:
        return None
    pick = None
    for _ in range(300):
        cand = rng.sample(range(m), r)
        xs = {E[i][0] for i in cand}
        ys = {E[i][1] for i in cand}
        if len(xs) == r and len(ys) == r:
            pick = cand
            break
    if pick is None:
        return None

    a, b = n, n + 1
    xs = [E[i][0] for i in pick]
    ys = [E[i][1] for i in pick]
    drop = set(pick)
    E2 = [E[i] for i in range(m) if i not in drop]
    E2.append((a, b))
    E2.extend((x, b) for x in xs)
    E2.extend((a, y) for y in ys)
    n2 = n + 2
    eset = set(E2)
    if len(eset) != len(E2):
        return None
    m2 = len(E2)

    cost = _bad_pairs(n2, _adjacency(n2, E2), D)
    T0, T1 = 0.7, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m2)
        j = rng.randrange(m2)
        if i == j:
            continue
        u1, v1 = E2[i]
        u2, v2 = E2[j]
        if u1 == u2 or v1 == v2:
            continue
        e1 = (u1, v2)
        e2 = (u2, v1)
        if e1 in eset or e2 in eset:
            continue
        E2[i] = e1
        E2[j] = e2
        eset.discard((u1, v1))
        eset.discard((u2, v2))
        eset.add(e1)
        eset.add(e2)
        new_cost = _bad_pairs(n2, _adjacency(n2, E2), D)
        T = T0 * (T1 / T0) ** (it / iters)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            E2[i] = (u1, v1)
            E2[j] = (u2, v2)
            eset.discard(e1)
            eset.discard(e2)
            eset.add((u1, v1))
            eset.add((u2, v2))

    if cost == 0:
        return n2, E2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Cheap base: projective plane incidence graph for D >= 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Phase 1: annealed group voltage lifts to find a strong base.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    lift_deadline = start + 0.4 * total
    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, lift_deadline, 1200)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: repeated edge-switch growth from the current best graph.
    if d >= 2:
        while time.monotonic() < deadline:
            res = _grow_once(best_n, best[1], d, D, rng, 2000, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
