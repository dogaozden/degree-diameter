import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective-plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Every vertex has degree d, so the lift is a regular bipartite seed.
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
            c2 = _cost(k, G, D, darts, perms)
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
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _lift_stage(d, D, deadline, rng):
    """Search annealed lifts until the deadline; return the largest valid lift found, or None."""
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    found = None
    best_n = 2 * d
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None and res[0] > best_n:
            found = res
            best_n = res[0]
    return found


# ----------------------------------------------------------------------------
# NEW: splice-and-repair growth.
#
# Given a d-regular bipartite graph with diameter <= D, add one left vertex x and
# one right vertex y. Pick d edges (a_i, b_i) forming a matching, delete them, and
# join x to every b_i and y to every a_i. Degrees stay exactly d, and the order
# grows by 2. The new graph is usually too far from diameter D, so a double-edge
# swap annealing (which keeps degrees and the bipartition) drives the number of
# bad pairs to zero. Each success becomes the next seed.
# ----------------------------------------------------------------------------

def _adjacency(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (disconnected pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _two_color(n, adj):
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


def _splice(n, E, d, rng):
    """Add a left vertex and a right vertex by splicing out a random d-matching. None if not d-regular."""
    adj = _adjacency(n, E)
    if any(len(a) != d for a in adj):
        return None
    color = _two_color(n, adj)
    edges = [(u, v) if color[u] == 0 else (v, u) for u, v in E]  # oriented (left, right)
    order = list(range(len(edges)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        a, b = edges[idx]
        if a in used_a or b in used_b:
            continue
        chosen.append(idx)
        used_a.add(a)
        used_b.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    x, y = n, n + 1
    removed = set(chosen)
    new_edges = [e for i, e in enumerate(edges) if i not in removed]
    for idx in chosen:
        a, b = edges[idx]
        new_edges.append((x, b))
        new_edges.append((a, y))
    return n + 2, new_edges


def _repair(n, E, d, D, deadline, rng, iters):
    """Double-edge-swap annealing on oriented edges (left, right). Returns edges with cost 0, or None."""
    edges = list(E)
    m = len(edges)
    pairs = set(edges)
    adj = _adjacency(n, edges)
    cost = _bad_pairs(n, adj, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in pairs or (a2, b1) in pairs:
            continue
        edges[i] = (a1, b2)
        edges[j] = (a2, b1)
        c2 = _bad_pairs(n, _adjacency(n, edges), D)
        T = 2.0 * (1.0 - it / iters) + 0.1
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            pairs.discard((a1, b1))
            pairs.discard((a2, b2))
            pairs.add((a1, b2))
            pairs.add((a2, b1))
            cost = c2
        else:
            edges[i] = (a1, b1)
            edges[j] = (a2, b2)
    if cost == 0:
        return edges
    return None


def _grow(n, E, d, D, deadline, rng, consider, iters):
    """Repeatedly splice and repair, reporting each valid success through consider()."""
    cur_n, cur_E = n, E
    misses = 0
    while time.monotonic() < deadline:
        sp = _splice(cur_n, cur_E, d, rng)
        if sp is None:
            misses += 1
            if misses > 200:
                break
            continue
        n2, E2 = sp
        res = _repair(n2, E2, d, D, deadline, rng, iters)
        if res is None:
            misses += 1
            continue
        cur_n, cur_E = n2, res
        consider(cur_n, cur_E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: d-regular, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, list(E))

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # Moore-tight for D = 3 when d - 1 is a prime power: nothing more to gain.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    try:
        lift = _lift_stage(d, D, start + 0.3 * time_limit, rng)
        if lift is not None:
            consider(lift[0], lift[1])
    except Exception:
        pass

    try:
        _grow(best[0], list(best[1]), d, D, start + 0.85 * time_limit, rng, consider, 3000)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
