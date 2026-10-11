import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Search family: d-regular bipartite graphs, grown by two vertices at a time
# and repaired by degree-preserving edge swaps (simulated annealing on the
# number of vertex pairs at distance > D).
#
# Side convention: vertices < n/2 form side 0 (stored first in every edge),
# and every new vertex pair is (side-0 vertex x, side-1 vertex y). Edge swaps
# keep degrees and bipartiteness, so the output is always d-regular and
# bipartite by construction.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
    """Number of ordered (vertex, unreached vertex) pairs at distance > D. Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(n, E, adj, D, rng, t_end, T0=4.0, T1=0.3):
    """Degree-preserving edge-swap annealing with a time-based temperature schedule.

    Returns True as soon as the diameter condition holds, False at t_end.
    E and adj are updated in place.
    """
    cost = _cost(n, adj, D)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-6, t_end - t0)
    m = len(E)
    while True:
        now = time.monotonic()
        if now >= t_end:
            return False
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        for _ in range(16):
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            # Apply swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
            adj[a1].discard(b1); adj[b1].discard(a1)
            adj[a2].discard(b2); adj[b2].discard(a2)
            adj[a1].add(b2); adj[b2].add(a1)
            adj[a2].add(b1); adj[b1].add(a2)
            c2 = _cost(n, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                E[i] = (a1, b2)
                E[j] = (a2, b1)
                cost = c2
                if cost == 0:
                    return True
            else:
                # Revert.
                adj[a1].discard(b2); adj[b2].discard(a1)
                adj[a2].discard(b1); adj[b1].discard(a2)
                adj[a1].add(b1); adj[b1].add(a1)
                adj[a2].add(b2); adj[b2].add(a2)


def _grow(n, E, adj, k, rng):
    """Add two vertices x (side 0) and y (side 1), each of degree k, by rerouting k disjoint edges.

    Requires k edges with pairwise distinct side-0 and side-1 endpoints. Returns the new n, or None.
    Edits E and adj in place.
    """
    m = len(E)
    if m < k:
        return None
    pick = None
    for _ in range(500):
        idx = rng.sample(range(m), k)
        As = {E[t][0] for t in idx}
        Bs = {E[t][1] for t in idx}
        if len(As) == k and len(Bs) == k:
            pick = idx
            break
    if pick is None:
        return None
    pairs = [E[t] for t in pick]
    chosen = set(pick)
    E[:] = [e for t, e in enumerate(E) if t not in chosen]
    for a, b in pairs:
        adj[a].discard(b)
        adj[b].discard(a)
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    for a, b in pairs:
        E.append((x, b))
        adj[x].add(b); adj[b].add(x)
        E.append((a, y))
        adj[a].add(y); adj[y].add(a)
    return n + 2


def _search(base_n, base_E, d, D, deadline, rng, consider):
    """Grow and anneal a d-regular bipartite graph, reporting each valid size via consider()."""
    n = base_n
    E = list(base_E)
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)

    failures = 0
    while time.monotonic() < deadline and failures < 3:
        now = time.monotonic()
        remaining = deadline - now
        budget = min(remaining, max(2.0, 0.35 * remaining))
        t_end = now + budget

        nE = list(E)
        nadj = [set(s) for s in adj]
        nn = _grow(n, nE, nadj, d, rng)
        if nn is None:
            break

        if _anneal(nn, nE, nadj, D, rng, t_end):
            n, E, adj = nn, nE, nadj
            consider(n, list(E))
            failures = 0
        else:
            failures += 1


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular, bipartite, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Base: projective plane incidence when d-1 is a prime power (diameter 3, d-regular).
    base = None
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        pg_n, pg_e = lib.projective_plane_incidence(d - 1)
        consider(pg_n, pg_e)
        base = (pg_n, pg_e)

    # Main bold search: regular bipartite growth with annealed repair (D >= 4).
    if D >= 4:
        if base is None and d >= 4:
            base = best
        if base is not None:
            _search(base[0], base[1], d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
