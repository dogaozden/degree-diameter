import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _colors(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists (-1 for isolated/uncoloured)."""
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
# D = 3 family: edge-move annealing that tries to extend a valid bipartite graph
# by two vertices (one per side) while keeping max degree d and diameter <= 3.
#
# Moves keep the bipartition fixed:
#   swap: (a,b),(c,e) -> (a,e),(c,b)  (degrees unchanged)
#   fill: (c,e) -> (a,e) and add (c,b), where a and b are deficient (degree < d).
# Cost = number of unordered vertex pairs at distance > D. Zero means valid.
# ----------------------------------------------------------------------------

def _bad_pairs_sets(n, adj, D):
    """Number of unordered pairs at distance > D; adj is a list of neighbour collections."""
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


def _anneal_extend(n, edges, color, d, D, deadline, rng):
    """Search for a valid bipartite graph on n vertices, starting from the given edges."""
    adj = [set() for _ in range(n)]
    deg = [0] * n
    E = set()
    elist = []

    def ad(a, b):
        E.add((a, b))
        adj[a].add(b)
        adj[b].add(a)
        deg[a] += 1
        deg[b] += 1

    def rm(a, b):
        E.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
        deg[a] -= 1
        deg[b] -= 1

    for u, v in edges:
        a, b = (u, v) if color[u] == 0 else (v, u)
        if (a, b) in E:
            continue
        ad(a, b)
        elist.append([a, b])
    if deg and max(deg) > d:
        return None

    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    cost = _bad_pairs_sets(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (0.02 ** ((now - t0) / span))

        if rng.random() < 0.25:
            # Fill move: raise the degrees of a deficient A-vertex and B-vertex.
            defA = [a for a in A if deg[a] < d]
            defB = [b for b in B if deg[b] < d]
            if not defA or not defB or not elist:
                continue
            a = rng.choice(defA)
            b = rng.choice(defB)
            i = rng.randrange(len(elist))
            c, e = elist[i]
            if c == a or e == b or (a, e) in E or (c, b) in E:
                continue
            rm(c, e)
            ad(a, e)
            ad(c, b)
            elist[i] = [a, e]
            elist.append([c, b])
            c2 = _bad_pairs_sets(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                rm(a, e)
                rm(c, b)
                ad(c, e)
                elist[i] = [c, e]
                elist.pop()
        else:
            # Swap move: degree-preserving 2-switch.
            if len(elist) < 2:
                continue
            i, j = rng.sample(range(len(elist)), 2)
            a, b = elist[i]
            c, e = elist[j]
            if a == c or b == e or (a, e) in E or (c, b) in E:
                continue
            rm(a, b)
            rm(c, e)
            ad(a, e)
            ad(c, b)
            elist[i] = [a, e]
            elist[j] = [c, b]
            c2 = _bad_pairs_sets(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                rm(a, e)
                rm(c, b)
                ad(a, b)
                ad(c, e)
                elist[i] = [a, b]
                elist[j] = [c, e]

    if cost == 0:
        return n, [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# D >= 4 family: annealed bi-Cayley voltage lifts over semidirect products.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 6, 8, 12])
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


def _lift_cost(k, G, D, darts, perms, limit=float("inf")):
    """Pairs (representative, vertex) not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Metropolis annealing over voltages and B-assignments; returns (n, edges) or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms, limit)
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
            c2 = _lift_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Record family: Araujo-Pardo & Lopez for d = q + 2, else plain PG(2, q).
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Bold path: grow the best valid graph by two vertices at a time with
        # edge-move annealing, as long as the Moore bound allows it.
        bound = lib._moore_bound(d, D)
        cur_n, cur_e = best
        while time.monotonic() < deadline and cur_n + 2 <= bound:
            adj = [[] for _ in range(cur_n)]
            for u, v in cur_e:
                adj[u].append(v)
                adj[v].append(u)
            col = _colors(cur_n, adj)
            if any(c < 0 for c in col):
                break
            res = _anneal_extend(cur_n + 2, cur_e, col + [0, 1], d, D, deadline, rng)
            if res is None or not lib.is_valid(res[0], res[1], d, D):
                break
            cur_n, cur_e = res
            consider(cur_n, cur_e)

    if D >= 4:
        # Annealed group voltage lifts (small D is not the focus here).
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
