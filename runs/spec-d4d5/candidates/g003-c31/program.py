import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _adj_from(n, edges):
    """Adjacency lists for an edge list on vertices 0..n-1."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """A proper 2-colouring of a bipartite graph given by adjacency lists."""
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


def _oriented(n, edges):
    """Re-orient every edge as (side0, side1) using a 2-colouring."""
    color = _bipartition(n, _adj_from(n, edges))
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Base construction: projective plane incidence (diameter 3, Moore-optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k2, annealed (seed family).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Pairs (representative, vertex) not reached within D. Zero means valid."""
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


def _lift_edges(k, G, darts, perms):
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
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: grow-and-repair search.
#
# Growth: from a valid graph, add a vertex pair (u on side 0, w on side 1).
# Pick d-1 edges (a_i, b_i) with distinct endpoints, delete them, then add
# u-w, u-b_i and a_i-w. Every old degree is unchanged, u and w get degree d,
# and the graph stays bipartite with max degree d.
#
# Repair: anneal over degree-preserving bipartite 2-switches
# (a,b),(c,e) -> (a,e),(c,b), minimising the number of pairs at distance > D.
# Each growth starts close to valid, so the repair usually needs few moves.
# ----------------------------------------------------------------------------

def _grow_pair(n, elist, d, rng):
    """Return (n + 2, edges) with one new side-0 and one new side-1 vertex, or None."""
    idxs = list(range(len(elist)))
    rng.shuffle(idxs)
    used_a, used_b, chosen = set(), set(), []
    for i in idxs:
        a, b = elist[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    rem = set(chosen)
    E = [e for i, e in enumerate(elist) if i not in rem]
    u, w = n, n + 1
    E.append((u, w))
    for i in chosen:
        a, b = elist[i]
        E.append((u, b))
        E.append((a, w))
    return n + 2, E


def _repair(n, edges, D, deadline, rng, iters):
    """Anneal 2-switches to minimise bad pairs. Returns (best_cost, best_edges)."""
    E = list(edges)
    eset = set(E)
    adj = _adj_from(n, E)
    cost = _bad_pairs(n, adj, D)
    best_cost, best_E = cost, list(E)
    m = len(E)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in eset or (c, b) in eset:
            continue
        adj[a].remove(b); adj[b].remove(a)
        adj[c].remove(e); adj[e].remove(c)
        adj[a].append(e); adj[e].append(a)
        adj[c].append(b); adj[b].append(c)
        new = _bad_pairs(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            eset.discard((a, b)); eset.discard((c, e))
            eset.add((a, e)); eset.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
            cost = new
            if cost < best_cost:
                best_cost, best_E = cost, list(E)
        else:
            adj[a].remove(e); adj[e].remove(a)
            adj[c].remove(b); adj[b].remove(c)
            adj[a].append(b); adj[b].append(a)
            adj[c].append(e); adj[e].append(c)
    return best_cost, best_E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Calibration cases that already meet the Moore bound return immediately.
    if best_n >= moore:
        return best_n, best_e

    # Phase 1: voltage-lift seeds (40% of the search budget).
    seed_deadline = start + 0.4 * (deadline - start)
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < seed_deadline and best_n < moore:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, seed_deadline, iters=1200)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: grow-and-repair from the best valid graph.
    if D >= 3:
        while time.monotonic() < deadline and best_n < moore:
            elist = _oriented(best_n, best_e)
            grown = _grow_pair(best_n, elist, d, rng)
            if grown is None:
                break
            n1, E1 = grown
            cost, E2 = _repair(n1, E1, D, deadline, rng, iters=2000)
            if cost == 0:
                consider(n1, E2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
