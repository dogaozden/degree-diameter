"""Growth-and-repair annealing for bipartite regular graphs with bounded diameter.

New idea (not used by the parent): keep a d-regular bipartite graph with N vertices
per side that already has diameter <= D. Grow it by one vertex per side with a
"matching split": pick a matching of d edges (distinct endpoints), delete them, and
join the new A-vertex to their B-ends and the new B-vertex to their A-ends. Degrees
stay exactly d. The result usually violates the diameter bound only slightly, so a
2-switch annealer (degree-preserving edge swaps, cost = number of vertex pairs at
distance > D) repairs it. Some attempts start instead from a random Haar-type circulant
at the target size, which gives diversity.
"""
import math
import random
import time

import lib


def _ball_cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _make_state(N, edges):
    adj = [[] for _ in range(2 * N)]
    eset = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        eset.add((u, v))
    return adj, eset


def _set_edge(adj, eset, edges, i, nu, nv):
    """Replace edges[i] by (nu, nv), keeping adjacency and edge set in sync."""
    ou, ov = edges[i]
    adj[ou].remove(ov)
    adj[ov].remove(ou)
    eset.discard((ou, ov))
    adj[nu].append(nv)
    adj[nv].append(nu)
    eset.add((nu, nv))
    edges[i] = (nu, nv)


def _anneal(N, d, D, edges, rng, deadline, iters):
    """2-switch annealing on a d-regular bipartite graph (A ids 0..N-1, B ids N..2N-1).

    Degree-preserving swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Returns a list of
    edges with diameter <= D, or None.
    """
    n = 2 * N
    edges = list(edges)
    adj, eset = _make_state(N, edges)
    cost = _ball_cost(n, adj, D)
    m = len(edges)
    T0, T1 = 1.5, 0.15
    decay = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= decay
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _set_edge(adj, eset, edges, i, a1, b2)
        _set_edge(adj, eset, edges, j, a2, b1)
        c2 = _ball_cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _set_edge(adj, eset, edges, j, a2, b2)
            _set_edge(adj, eset, edges, i, a1, b1)
    return list(edges) if cost == 0 else None


def _extend(N, d, edges, rng):
    """Matching-split growth: add one vertex per side, keeping the graph d-regular.

    Chooses d edges with pairwise distinct endpoints, replaces each (u, v) by
    (new_A, v) and (u, new_B). Returns (N+1, edges) in the new numbering, or None.
    """
    idx = list(range(len(edges)))
    rng.shuffle(idx)
    chosen = []
    used_a, used_b = set(), set()
    for i in idx:
        u, v = edges[i]
        if u in used_a or v in used_b:
            continue
        chosen.append(i)
        used_a.add(u)
        used_b.add(v)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    new_a = N
    new_b = 2 * N + 1  # B ids shift by one: old B v -> v + 1
    out = []
    for i, (u, v) in enumerate(edges):
        if i in chosen_set:
            out.append((new_a, v + 1))
            out.append((u, new_b))
        else:
            out.append((u, v + 1))
    return N + 1, out


def _haar_start(N, d, rng):
    """Random Haar-type d-regular bipartite graph on N + N vertices."""
    S = rng.sample(range(N), d)
    return [(i, N + (i + s) % N) for i in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Baseline: K_{d,d} (diameter 2, valid for D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    # D = 3 baseline: projective plane incidence when d-1 is a prime power (Moore-optimal).
    if D >= 3 and d >= 2 and lib.is_prime_power(d - 1):
        n2, e2 = lib.projective_plane_incidence(d - 1)
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2

    # Growth needs a d-regular starting graph whose sides are ids 0..N-1 and N..2N-1.
    deg = [0] * best_n
    for u, v in best_e:
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return best_n, [(int(u), int(v)) for u, v in best_e]

    N = best_n // 2
    cur = [(int(u), int(v)) for u, v in best_e]

    while time.monotonic() < deadline:
        if rng.random() < 0.75:
            ext = _extend(N, d, cur, rng)
            if ext is None:
                break
            N2, e2 = ext
        else:
            N2 = N + 1
            e2 = _haar_start(N2, d, rng)
        res = _anneal(N2, d, D, e2, rng, deadline, 2500)
        if res is not None and lib.is_valid(2 * N2, res, d, D):
            N, cur = N2, res

    best_n, best_e = 2 * N, cur
    if lib.is_valid(best_n, best_e, d, D):
        return best_n, [(int(u), int(v)) for u, v in best_e]
    return lib.haar_graph(d, range(d))
