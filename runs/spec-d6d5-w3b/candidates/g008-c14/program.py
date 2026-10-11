import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite regular graphs as side-indexed edge lists.
#
# A state is (m, E): left vertices 0..m-1, right vertices 0..m-1, and E a list
# of distinct pairs (a, b) meaning left a ~ right b. The output graph has
# n = 2m vertices, with right b relabelled as m + b.
# ----------------------------------------------------------------------------

def _bad_pairs(m, E, D):
    """Ordered count of vertex pairs at distance > D, via bitmask BFS."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
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


def _anneal(m, d, D, E, deadline, rng, T0=1.0, max_iters=10 ** 9):
    """2-switch simulated annealing on the bad-pair count.

    A switch replaces (a,b),(c,e) by (a,e),(c,b). Both sides keep their degrees
    and no duplicate edge is created. Returns (E or None, final_cost).
    """
    E = list(E)
    eset = set(E)
    cur = _bad_pairs(m, E, D)
    T = T0
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        T = max(0.05, T * 0.999)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = _bad_pairs(m, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return (E if cur == 0 else None), cur


def _splice(m, E, d, rng):
    """Add one left vertex m and one right vertex m, each of degree d, by splicing d edges.

    Chosen edges (a_i, b_i) have distinct a_i and distinct b_i. They are replaced
    by (m, b_i) and (a_i, m). All old degrees are kept. Returns (m+1, E) or None.
    """
    k = len(E)
    if k < d:
        return None
    x = m
    y = m
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 50000:
        tries += 1
        i = rng.randrange(k)
        if i in used:
            continue
        a, b = E[i]
        if b in xs or a in ys:
            continue
        used.add(i)
        xs.add(b)
        ys.add(a)
        chosen.append(i)
    if len(chosen) < d:
        return None
    newE = [E[i] for i in range(k) if i not in used]
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return m + 1, newE


def _circulant_start(m, d, rng):
    """A simple d-regular bipartite graph: left i ~ right i+s for d distinct shifts s."""
    shifts = rng.sample(range(m), d)
    return [(i, (i + s) % m) for i in range(m) for s in shifts]


def _ladder(d, D, deadline, rng, consider):
    """Random-start annealing with growth by splicing.

    Anneal a random d-regular bipartite graph on m+m vertices to diameter <= D,
    report it, splice in one more pair of vertices, and repeat. Stops at the
    first size the annealer cannot repair within its per-step budget.
    """
    m = max(d + 1, 8)
    E = _circulant_start(m, d, rng)
    while time.monotonic() < deadline:
        now = time.monotonic()
        cap = min(deadline, now + max(1.0, 0.25 * (deadline - now)))
        res, _ = _anneal(m, d, D, E, cap, rng)
        if res is None:
            break
        E = res
        consider(2 * m, [(a, m + b) for a, b in E])
        grown = _splice(m, E, d, rng)
        if grown is None:
            break
        m, E = grown


# ----------------------------------------------------------------------------
# Algebraic baselines, kept as the safe floor.
# ----------------------------------------------------------------------------

def _pg_incidence(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (diameter 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q+2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Cycle C_{2D}: bipartite, max degree 2, diameter D.
    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    if D >= 3:
        pg = _pg_incidence(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # New family for D >= 3: annealed random bipartite regular graphs grown by splicing.
    if D >= 3 and d >= 3:
        _ladder(d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
