import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold direction: repair search on bipartite graphs, not a fixed algebraic
# family. Start from a valid base (projective plane incidence, or K_{d,d}),
# then repeatedly add one vertex on each side, fill spare degree greedily, and
# anneal the edge set to zero bad ordered pairs at distance > D. Every solved
# stage is snapshotted; the final answer is always checked with lib.is_valid.
# ----------------------------------------------------------------------------


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d; returns (n, edges, m) or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, e = lib.projective_plane_incidence(q)
            return n, e, n // 2
    return None


def _reach_cost(n, nbr, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _fill(v, opp, nbr, d, rng):
    """Greedily join vertex v to random deficient opposite-side vertices."""
    cands = [w for w in opp if len(nbr[w]) < d and w not in nbr[v]]
    rng.shuffle(cands)
    for w in cands:
        if len(nbr[v]) >= d:
            break
        if len(nbr[w]) < d and w not in nbr[v]:
            nbr[v].add(w)
            nbr[w].add(v)


def _anneal(n, A, B, nbr, d, D, rng, deadline):
    """Metropolis search over A-B edge sets (degree <= d) minimizing _reach_cost.

    A move picks a random non-edge (a, b); overfull endpoints first drop one
    random incident edge, then (a, b) is added. Returns True once cost is zero
    (state left solved in place), False if the deadline passes first.
    """
    cur = _reach_cost(n, nbr, D)
    if cur == 0:
        return True
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    Tstart, Tend = 2.0, 0.2
    while True:
        now = time.monotonic()
        if now >= deadline:
            return False
        frac = (now - t0) / span
        T = Tstart * (Tend / Tstart) ** frac
        a = rng.choice(A)
        b = rng.choice(B)
        if b in nbr[a]:
            continue
        removed = []
        if len(nbr[a]) >= d:
            x = rng.choice(list(nbr[a]))
            nbr[a].discard(x)
            nbr[x].discard(a)
            removed.append((a, x))
        if len(nbr[b]) >= d:
            y = rng.choice(list(nbr[b]))
            nbr[b].discard(y)
            nbr[y].discard(b)
            removed.append((b, y))
        nbr[a].add(b)
        nbr[b].add(a)
        new = _reach_cost(n, nbr, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            if cur == 0:
                return True
        else:
            nbr[a].discard(b)
            nbr[b].discard(a)
            for p, q in removed:
                nbr[p].add(q)
                nbr[q].add(p)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 4.0)
    deadline = start + max(budget, 0.5)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n_c, e_c):
        nonlocal best, best
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)

    # Starting state: PG(2,q) incidence when D >= 3 (diameter 3), else K_{d,d}.
    base = _pg_base(d) if D >= 3 else None
    if base is not None:
        n, e, m = base
        consider(n, e)
        A = list(range(m))
        B = list(range(m, n))
    else:
        n, e = lib.haar_graph(d, range(d))
        A = list(range(d))
        B = list(range(d, 2 * d))

    nbr = [set() for _ in range(n)]
    for u, v in e:
        nbr[u].add(v)
        nbr[v].add(u)

    # Grow one vertex per side at a time; repair with annealing after each growth.
    while time.monotonic() < deadline:
        a = n
        b = n + 1
        n += 2
        nbr.append(set())
        nbr.append(set())
        A.append(a)
        B.append(b)
        _fill(a, B, nbr, d, rng)
        _fill(b, A, nbr, d, rng)

        if _reach_cost(n, nbr, D) > 0:
            solved = _anneal(n, A, B, nbr, d, D, rng, deadline)
            if not solved:
                break

        edges = [(x, y) for x in A for y in nbr[x]]
        consider(n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
