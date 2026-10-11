import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments (Metropolis via threshold)."""
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
# NEW: vertex insertion by edge splitting + edge-switch repair annealing.
#
# Keep a bipartite graph with all degrees <= d, objective = number of vertex
# pairs at distance > D. Two move types:
#   * switch: replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Degrees unchanged.
#   * insert: pick d-1 edges with pairwise distinct endpoints, remove them,
#     add a new A-vertex x joined to their B-ends and to a new B-vertex y,
#     and y joined to their A-ends. Both new vertices get degree d.
# When the cost hits zero, the graph is valid at its size, so grow it by
# insertion. On stagnation, restart from the last valid snapshot.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _orient(n, edges):
    """Return (side, E) where side is a 2-colouring and E lists edges as (A-end, B-end)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = _bipartition(n, adj)
    E = [(u, v) if side[u] == 0 else (v, u) for u, v in edges]
    return side, E


def _apply(adj, Es, old1, old2, new1, new2):
    """Remove edges old1, old2 and add edges new1, new2 in place."""
    for a, b in (old1, old2):
        adj[a].discard(b)
        adj[b].discard(a)
        Es.discard((a, b))
    for a, b in (new1, new2):
        adj[a].add(b)
        adj[b].add(a)
        Es.add((a, b))


def _insert(n, E, side, Es, adj, d, rng):
    """Vertex insertion by splitting d-1 edges with distinct endpoints. Returns new state or None."""
    m = len(E)
    order = list(range(m))
    rng.shuffle(order)
    chosen = []
    usedA, usedB = set(), set()
    for t in order:
        a, b = E[t]
        if a in usedA or b in usedB:
            continue
        chosen.append(t)
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    chosen_set = set(chosen)
    pairs = [E[t] for t in chosen]
    newE = [E[t] for t in range(m) if t not in chosen_set]
    for a, b in pairs:
        Es.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    side2 = side + [0, 1]
    added = [(x, b) for _, b in pairs] + [(a, y) for a, _ in pairs] + [(x, y)]
    for a, b in added:
        adj[a].add(b)
        adj[b].add(a)
        Es.add((a, b))
        newE.append((a, b))
    return n + 2, newE, side2, adj, Es


def _repair(d, D, n, edges, deadline, rng):
    """Anneal edge switches with growth by insertion. Returns the largest valid (n, edges) found."""
    side, E = _orient(n, edges)
    adj = [set() for _ in range(n)]
    Es = set(E)
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cur = _bad(n, adj, D)
    best = (n, list(E)) if cur == 0 else None
    snap = (n, list(E), list(side))
    stall = 0
    T = 0.5

    while time.monotonic() < deadline:
        if cur == 0:
            best = (n, list(E))
            snap = (n, list(E), list(side))
            ins = _insert(n, E, side, Es, adj, d, rng)
            if ins is None:
                break
            n, E, side, adj, Es = ins
            cur = _bad(n, adj, D)
            stall = 0
            continue

        m = len(E)
        if m < 2:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in Es or (a2, b1) in Es:
            continue
        old1, old2 = (a1, b1), (a2, b2)
        new1, new2 = (a1, b2), (a2, b1)
        _apply(adj, Es, old1, old2, new1, new2)
        c2 = _bad(n, adj, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            E[i] = new1
            E[j] = new2
            cur = c2
        else:
            _apply(adj, Es, new1, new2, old1, old2)

        stall += 1
        if stall > 4000 and cur > 0:
            n, E, side = snap[0], list(snap[1]), list(snap[2])
            adj = [set() for _ in range(n)]
            Es = set(E)
            for a, b in E:
                adj[a].add(b)
                adj[b].add(a)
            cur = _bad(n, adj, D)
            stall = 0

    if best is None:
        return None
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Phase 1: annealed group voltage lifts.
    lift_deadline = start + 0.45 * time_limit
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < lift_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=1200)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: repair/growth search from the best graph found so far.
    if D >= 3 and time.monotonic() < start + 0.85 * time_limit:
        rep = _repair(d, D, best[0], best[1], start + 0.85 * time_limit, rng)
        if rep is not None:
            consider(rep[0], rep[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
