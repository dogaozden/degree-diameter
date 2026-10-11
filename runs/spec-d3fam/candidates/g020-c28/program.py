import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Degree-preserving edge-swap annealing that grows a diameter-D bipartite graph
# by one A-vertex and one B-vertex. Each new vertex is spliced into existing
# edges (x, y) -> (a*, y), (x, b*), which keeps every old degree unchanged.
# ----------------------------------------------------------------------------

def _color(n, edges):
    """Two-colouring of a graph given as an edge list (uncoloured vertices get 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad(n, E, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _extend(n, edges, d, D, deadline, rng):
    """Try to add two vertices (one per side) by annealing degree-preserving swaps.

    Returns (N, E) with N = n + 2 if a diameter-D graph was found, else None.
    """
    col = _color(n, edges)
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    A, B = n, n + 1
    N = n + 2
    E_set = set(E)
    nbA, nbB = set(), set()

    # Splice: remove (x, y), add (A, y) and (x, B). Old degrees are unchanged.
    for _ in range(d):
        cands = [i for i, (x, y) in enumerate(E) if y not in nbA and x not in nbB]
        if not cands:
            break
        i = rng.choice(cands)
        x, y = E[i]
        E[i] = (A, y)
        E_set.discard((x, y))
        E_set.add((A, y))
        E.append((x, B))
        E_set.add((x, B))
        nbA.add(y)
        nbB.add(x)

    M = len(E)
    if M < 2:
        return None
    cur = _bad(N, E, D)
    best_cost = cur
    best_E = list(E)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in E_set or n2 in E_set:
            continue
        E[i] = n1
        E[j] = n2
        E_set.discard((a1, b1))
        E_set.discard((a2, b2))
        E_set.add(n1)
        E_set.add(n2)

        new = _bad(N, E, D)
        frac = (time.monotonic() - t0) / span
        T = 2.0 * (0.03 ** min(1.0, frac))
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best_cost:
                best_cost = cur
                best_E = list(E)
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            E_set.discard(n1)
            E_set.discard(n2)
            E_set.add((a1, b1))
            E_set.add((a2, b2))

    if best_cost == 0:
        return N, best_E
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # PG(2, q) incidence graph has diameter 3.
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass

        # New family: repeatedly grow by two vertices via annealed swaps.
        budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
        deadline = start + budget
        rng = random.Random(seed)
        try:
            cur = best
            while time.monotonic() < deadline - 0.5:
                res = _extend(cur[0], cur[1], d, D, deadline, rng)
                if res is None:
                    break
                consider(res[0], res[1])
                if best[0] == res[0]:
                    cur = res
                else:
                    break
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
