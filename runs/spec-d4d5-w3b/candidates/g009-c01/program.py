"""Edge-switch annealing over random d-regular bipartite graphs.

Earlier versions searched bi-Cayley voltage lifts. This version instead
starts from a random d-regular bipartite graph on sides of size N and
anneals double edge switches (which keep every degree fixed and the graph
bipartite), minimizing the number of vertex pairs at distance > D. N is
increased whenever a zero-cost graph is found. A projective-plane incidence
graph (when D >= 3) and K_{d,d} serve as safe fallbacks, and every returned
graph is checked with lib.is_valid.
"""
import math
import random
import time

import lib


def _pg_candidate(d, D):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    if D < 3:
        return None
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _random_regular(N, d, rng):
    """Edge set of a simple d-regular bipartite graph on sides 0..N-1 (union of d perfect matchings)."""
    E = set()
    for _ in range(d):
        for _attempt in range(300):
            perm = list(range(N))
            rng.shuffle(perm)
            new = [(a, perm[a]) for a in range(N)]
            if not any(e in E for e in new):
                E.update(new)
                break
        else:
            return None
    return list(E)


def _bad(N, el, D):
    """Number of unordered vertex pairs at distance > D. A-vertex a is 'a'; B-vertex b is N + b."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in el:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(N, d, D, rng, budget, deadline):
    """Anneal double edge switches on a random d-regular bipartite graph; return edge list (a, b) or None."""
    E = _random_regular(N, d, rng)
    if E is None:
        return None
    el = list(E)
    eset = set(E)
    m = len(el)
    cost = _bad(N, el, D)
    t0 = time.monotonic()
    end = min(deadline, t0 + budget)
    while cost > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t0) / max(1e-9, end - t0)
        T = 1.0 * (1.0 - frac) + 0.05 * frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        el[i] = n1
        el[j] = n2
        new_cost = _bad(N, el, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add(n1)
            eset.add(n2)
            cost = new_cost
        else:
            el[i] = (a1, b1)
            el[j] = (a2, b2)
    return el if cost == 0 else None


def _search(d, D, deadline, rng, state, consider, bound, total):
    """Grow N: anneal a zero-cost d-regular bipartite graph on 2N vertices, then try N + 1."""
    N = max(d, state['best'][0] // 2 + 1)
    while time.monotonic() < deadline and 2 * N <= bound:
        remaining = deadline - time.monotonic()
        budget = max(2.0, min(remaining, 0.25 * total))
        el = _anneal(N, d, D, rng, budget, deadline)
        if el is not None:
            edges = [(a, N + b) for a, b in el]
            consider(2 * N, edges)
            N += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 1000003 + d * 101 + D)
    deadline = start + 0.75 * time_limit
    bound = lib.moore_bound(d, D)
    state = {'best': (1, [])}

    def consider(n, e):
        if n > state['best'][0] and lib.is_valid(n, e, d, D):
            state['best'] = (n, e)
            return True
        return False

    # Safe fallback: K_{d,d}, valid for D >= 2.
    consider(*lib.haar_graph(d, range(d)))

    try:
        pg = _pg_candidate(d, D)
        if pg is not None:
            consider(*pg)
        if state['best'][0] < bound and time.monotonic() < deadline:
            _search(d, D, deadline, rng, state, consider, bound, 0.75 * time_limit)
    except Exception:
        pass  # keep the best valid graph found so far

    n, e = state['best']
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
