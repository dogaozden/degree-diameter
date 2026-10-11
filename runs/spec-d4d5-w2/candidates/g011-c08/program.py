import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured fallbacks (always tried first, always validated).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY: unstructured search over d-regular bipartite graphs.
#
# Instead of imposing a group action (voltage lifts / Haar graphs), this
# searches directly over d-regular bipartite graphs on h + h vertices.
# Moves are 2-switches (a1-b1, a2-b2  ->  a1-b2, a2-b1), which keep every
# degree exactly d and keep the graph bipartite and simple. The cost is the
# number of ordered vertex pairs not within distance D (zero means valid).
# Annealing runs at a fixed h; when a zero-cost graph appears, h is raised.
# ----------------------------------------------------------------------------

def _cost(n, D, adj):
    """Number of ordered pairs (u, v) with dist(u, v) > D. Zero means diameter <= D and connected."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal_regular(h, d, D, rng, deadline, iters):
    """Anneal a d-regular bipartite graph on h + h vertices toward diameter <= D; return edges or None."""
    n = 2 * h
    shifts = rng.sample(range(h), d)           # distinct shifts -> simple circulant start
    E = [[a, h + (a + s) % h] for a in range(h) for s in shifts]
    Eset = {(a, b) for a, b in E}
    m = len(E)

    def adj_of():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(b)
            adj[b].append(a)
        return adj

    def try_switch(i, j):
        """Attempt the 2-switch on edges i and j; return the undo data or None if illegal."""
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        if (a1, b2) in Eset or (a2, b1) in Eset:
            return None
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        Eset.difference_update({(a1, b1), (a2, b2)})
        Eset.update({(a1, b2), (a2, b1)})
        return (i, j, a1, b1, a2, b2)

    def undo(data):
        i, j, a1, b1, a2, b2 = data
        E[i] = [a1, b1]
        E[j] = [a2, b2]
        Eset.difference_update({(a1, b2), (a2, b1)})
        Eset.update({(a1, b1), (a2, b2)})

    # Scramble the circulant so different restarts explore different graphs.
    for _ in range(2 * m):
        i, j = rng.randrange(m), rng.randrange(m)
        if i != j:
            try_switch(i, j)

    cur = _cost(n, D, adj_of())
    T0, T_end = 3.0, 0.3
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        data = try_switch(i, j)
        if data is None:
            continue
        c2 = _cost(n, D, adj_of())
        delta = c2 - cur
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            undo(data)

    if cur == 0:
        return [(a, b) for a, b in E]
    return None


def _regular_search(d, D, best_n, deadline, rng, consider):
    """Repeatedly anneal at increasing h, starting slightly below the current best order."""
    h = max(d, best_n // 2 - 4)
    while time.monotonic() < deadline:
        edges = _anneal_regular(h, d, D, rng, deadline, iters=3000)
        if edges is not None:
            consider(2 * h, edges)
            h += 1
        # On failure we retry the same h with a fresh random start.


# ----------------------------------------------------------------------------
# Orchestration.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
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
        # Araujo-Pardo & Lopez record family for d = q + 2 with q a prime power.
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Bold change for D >= 4: unstructured annealing over regular bipartite graphs.
    if D >= 4 and d >= 3:
        try:
            _regular_search(d, D, best_n, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
