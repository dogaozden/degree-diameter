import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective-plane incidence graph and K_{d,d}.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _even(x):
    return x + (x % 2)


# ----------------------------------------------------------------------------
# Unstructured search: random bipartite graph on N + N vertices, degree <= d,
# improved by degree-preserving double-edge swaps (simulated annealing) on the
# number of vertex pairs at distance > D. Bipartiteness holds by construction
# (left vertices are 0..N-1, right vertices are N..2N-1).
# ----------------------------------------------------------------------------

def _balls(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad_per_vertex(n, adj, D):
    return [n - b.bit_count() for b in _balls(n, adj, D)]


def _adj_from(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _random_bip(N, d, rng):
    """Union of d random perfect matchings between the two sides (duplicates dropped)."""
    edges = set()
    for _ in range(d):
        perm = list(range(N, 2 * N))
        rng.shuffle(perm)
        for i in range(N):
            edges.add((i, perm[i]))
    return list(edges)


def _saturate(N, E, d, rng):
    """Greedily add edges between deficient opposite-side vertices (only adds edges)."""
    E = list(E)
    deg = [0] * (2 * N)
    eset = set(E)
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    L = [v for v in range(N) if deg[v] < d]
    R = [v for v in range(N, 2 * N) if deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (a, b) not in eset]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            eset.add((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


def _set_edge(adj, eset, E, idx, a, b):
    """Replace edge number idx by (a, b), keeping adjacency lists and edge set in sync."""
    a0, b0 = E[idx]
    adj[a0].remove(b0)
    adj[b0].remove(a0)
    eset.discard((a0, b0))
    adj[a].append(b)
    adj[b].append(a)
    eset.add((a, b))
    E[idx] = (a, b)


def _anneal(N, d, D, rng, deadline):
    """Anneal a random near-regular bipartite graph. Returns (edges_or_None, best_edges, best_cost)."""
    n = 2 * N
    E = [tuple(e) for e in _saturate(N, _random_bip(N, d, rng), d, rng)]
    if len(E) < 2:
        return None, E, 0
    eset = set(E)
    adj = _adj_from(n, E)
    cost = sum(_bad_per_vertex(n, adj, D))
    best_cost, best_E = cost, list(E)
    m = len(E)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    T0 = 1.5

    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _set_edge(adj, eset, E, i, a1, b2)
        _set_edge(adj, eset, E, j, a2, b1)
        new = sum(_bad_per_vertex(n, adj, D))
        frac = (time.monotonic() - start) / span
        T = max(0.05, T0 * (1.0 - frac))
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
        else:
            _set_edge(adj, eset, E, i, a1, b1)
            _set_edge(adj, eset, E, j, a2, b2)

    if cost == 0:
        return list(E), best_E, 0
    return None, best_E, best_cost


def _compact(n, E, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    return len(new), [(new[a], new[b]) for a, b in E if keep[a] and keep[b]]


def _repair(n, E, d, D, deadline):
    """Delete the vertices involved in the most bad pairs until diameter <= D. Returns (n, edges) or None."""
    cur_n, cur_E = n, list(E)
    while time.monotonic() < deadline:
        if cur_n < 2:
            return None
        adj = _adj_from(cur_n, cur_E)
        bad = _bad_per_vertex(cur_n, adj, D)
        if not any(bad):
            return cur_n, cur_E
        nbad = sum(1 for x in bad if x > 0)
        k = max(1, nbad // 10)
        order = sorted(range(cur_n), key=lambda v: -bad[v])
        dead = set(order[:k])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_E = _compact(cur_n, cur_E, keep)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Calibration-style small cases return the algebraic baseline immediately.
    if D < 4:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # Bold branch for D >= 4: annealed unstructured bipartite graphs with a growing target size.
    moore = lib.moore_bound(d, D)
    total = _even(max(best_n + 2, int(0.42 * moore)))
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        N = total // 2
        res, best_E, _ = _anneal(N, d, D, rng, now + 0.6 * remaining)
        if res is not None:
            consider(2 * N, res)
            total = _even(max(total, int(total * 1.03)))
        else:
            now = time.monotonic()
            rem = deadline - now
            if best_E and rem > 0.5:
                rep = _repair(2 * N, best_E, d, D, now + 0.5 * rem)
                if rep is not None:
                    consider(rep[0], rep[1])
            total = _even(max(best_n + 2, int(total * 0.97)))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
