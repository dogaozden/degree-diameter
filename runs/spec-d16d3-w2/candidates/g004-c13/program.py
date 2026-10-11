import math
import random
import time

import lib


def _smallest_pp_at_least(x):
    """Smallest prime power q >= x (and >= 2)."""
    q = max(2, x)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _pg_adj(q):
    """Incidence graph of PG(2, q) as (N, adjacency lists)."""
    n2, edges = lib.projective_plane_incidence(q)
    adj = [[] for _ in range(n2)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return n2, adj


def _alive_cost(N, adj, alive, need, D):
    """Cost of the induced subgraph on alive vertices.

    need = (base degree) - d: each alive vertex must lose at least `need` neighbours
    to deletion so that its degree is at most d. Cost = (unordered pairs at distance
    > D inside the alive subgraph) + 2 * (total degree deficit). Zero means valid.
    """
    alive_list = [v for v in range(N) if alive[v]]
    n_alive = len(alive_list)
    deficit = 0
    for v in alive_list:
        dead_nb = 0
        for u in adj[v]:
            if not alive[u]:
                dead_nb += 1
        if dead_nb < need:
            deficit += need - dead_nb
    reach = [0] * N
    for v in alive_list:
        reach[v] = 1 << v
    for _ in range(D):
        new = [0] * N
        for v in alive_list:
            x = reach[v]
            for u in adj[v]:
                if alive[u]:
                    x |= reach[u]
            new[v] = x
        reach = new
    bad2 = 0
    for v in alive_list:
        bad2 += n_alive - reach[v].bit_count()
    return bad2 // 2 + 2 * deficit


def _anneal(N, adj, need, D, dead, rng, deadline):
    """Simulated annealing over the deleted set `dead` (fixed size).

    Moves swap a deleted vertex with an alive one. Returns the deleted list when the
    alive subgraph is valid, otherwise None.
    """
    dead = list(dead)
    alive = [True] * N
    for x in dead:
        alive[x] = False
    cost = _alive_cost(N, adj, alive, need, D)
    if cost == 0:
        return dead
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 2.0, 0.05
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(len(dead))
        x = dead[i]
        y = rng.randrange(N)
        while not alive[y]:
            y = rng.randrange(N)
        alive[x] = True
        alive[y] = False
        c2 = _alive_cost(N, adj, alive, need, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            dead[i] = y
            if cost == 0:
                return dead
        else:
            alive[y] = True
            alive[x] = False
    return None


def _alive_graph(N, adj, dead):
    """Relabelled (n, edges) of the subgraph of the PG incidence graph without `dead`."""
    dead_set = set(dead)
    ids = {}
    for v in range(N):
        if v not in dead_set:
            ids[v] = len(ids)
    edges = []
    for u in ids:
        for v in adj[u]:
            if u < v and v in ids:
                edges.append((ids[u], ids[v]))
    return len(ids), edges


def _deletion_search(q, d, D, rng, deadline, best_n, consider):
    """Shrink PG(2, q) incidence graph (degree q+1 > d) by deleting vertices.

    Starts from a random deletion set, anneals to a valid alive subgraph, then
    ratchets the alive count upward by 2, warm-starting from the previous solution.
    """
    N, adj = _pg_adj(q)
    need = q + 1 - d
    moore = lib.moore_bound(d, D)
    dead = None
    n_t = best_n + 2
    while time.monotonic() < deadline and n_t <= moore and n_t <= N:
        K = N - n_t
        if dead is None:
            init = rng.sample(range(N), K)
        else:
            init = list(dead)
            for _ in range(2):
                if init:
                    init.pop(rng.randrange(len(init)))
            if len(init) < K:
                extra = [v for v in range(N) if v not in set(init)]
                rng.shuffle(extra)
                init += extra[:K - len(init)]
        now = time.monotonic()
        att_deadline = min(deadline, now + max(3.0, 0.5 * (deadline - now)))
        res = _anneal(N, adj, need, D, init, rng, att_deadline)
        if res is None:
            break
        dead = res
        n, e = _alive_graph(N, adj, dead)
        consider(n, e)
        n_t = n + 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)

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
        # Plain projective plane with q + 1 <= d (always valid for D >= 3).
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    if D == 3:
        # Bold change: start from PG(2, q) with q + 1 >= d and delete vertices
        # until the maximum degree drops to d, instead of adding to a smaller plane.
        q = _smallest_pp_at_least(max(2, d - 1))
        if 2 <= q <= 27 and q + 1 >= d:
            if q + 1 == d:
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
            else:
                rng = random.Random(seed * 1009 + d)
                _deletion_search(q, d, D, rng, deadline, best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
