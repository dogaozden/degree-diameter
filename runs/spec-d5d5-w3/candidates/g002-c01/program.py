import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Different construction from the parent: simulated annealing on bipartite
# graphs. Start from a random d-regular bipartite graph (a Haar graph with d
# distinct shifts) and apply degree-preserving double-edge swaps. The cost is
# the number of vertex pairs at distance > D, counted with big-int BFS balls.
# Sizes ratchet upward: each success at half-order h raises h, giving 2h vertices.
# ----------------------------------------------------------------------------

def _bad_pairs(n, nbr, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in nbr[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _haar_start(h, d, rng):
    """Random d-regular bipartite graph: left i joins right h + (i + s) mod h for d distinct shifts s."""
    shifts = rng.sample(range(h), d)
    return [[i, h + (i + s) % h] for i in range(h) for s in shifts]


def _anneal(h, d, D, rng, deadline):
    """Anneal degree-preserving swaps on a 2h-vertex d-regular bipartite graph.

    Returns (n, edges) with diameter <= D, or None if the deadline passes first.
    """
    n = 2 * h
    E = _haar_start(h, d, rng)
    nbr = [set() for _ in range(n)]
    for a, b in E:
        nbr[a].add(b)
        nbr[b].add(a)
    cur = _bad_pairs(n, nbr, D)
    t0 = time.monotonic()
    span = max(0.5, deadline - t0)
    frac = 0.0
    it = 0
    while cur > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now > deadline:
                break
            frac = min(1.0, (now - t0) / span)
        T = 0.2 + 0.8 * (1.0 - frac)

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]   # a left, b right
        c, e = E[j]   # c left, e right
        if e in nbr[a] or b in nbr[c]:
            continue
        # Replace (a,b),(c,e) by (a,e),(c,b).
        nbr[a].discard(b); nbr[b].discard(a)
        nbr[c].discard(e); nbr[e].discard(c)
        nbr[a].add(e); nbr[e].add(a)
        nbr[c].add(b); nbr[b].add(c)
        new = _bad_pairs(n, nbr, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            nbr[a].discard(e); nbr[e].discard(a)
            nbr[c].discard(b); nbr[b].discard(c)
            nbr[a].add(b); nbr[b].add(a)
            nbr[c].add(e); nbr[e].add(c)

    if cur == 0:
        return n, [(a, b) for a, b in E]
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic baseline for D = 3: incidence graph of PG(2, q), q + 1 <= d.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Ratchet the half-order upward with annealing.
    h = max(d + 1, moore // 8, best[0] // 2 + 1)
    while time.monotonic() < deadline and 2 * h <= moore:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, remaining / 3.0))
        res = _anneal(h, d, D, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])
            h += max(1, h // 100)
        else:
            # Retry the same order from a fresh random start.
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
