"""Edge-splice growth with double-edge-switch annealing.

Idea (new relative to the parent): keep a valid d-regular bipartite graph on
N + N vertices and grow it one vertex per side at a time. A new A-vertex and a
new B-vertex are inserted by splicing d disjoint edges (a_i, b_i): they become
(a_i, B_new) and (A_new, b_i), so every degree stays d. The inserted vertices
can break the diameter bound, so a double-edge-switch annealer repairs the graph.
The cost is the number of unordered vertex pairs at distance > D, computed with
bitmask balls. Each accepted state is a valid graph, so the best one is kept.
"""
import math
import random
import time

import lib


_T0 = 2.0          # annealing start temperature (in units of bad pairs)
_T1 = 0.25         # annealing end temperature
_CYCLE = 1500      # iterations per cooling cycle


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad(N, D, E):
    """Unordered vertex pairs at distance > D. A-vertex a is index a; B-vertex b is N + b."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt[v] = x
        if nxt == reach:
            break
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _repair(N, D, E, S, rng, deadline, iters):
    """Double-edge-switch annealing on E (list) and S (set of the same edges).

    Returns True if the bad-pair count reaches zero. Degrees are preserved by switches.
    """
    cost = _bad(N, D, E)
    m = len(E)
    it = 0
    while cost > 0 and it < iters:
        if time.monotonic() > deadline:
            break
        it += 1
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        frac = (it % _CYCLE) / _CYCLE
        T = _T0 * (_T1 / _T0) ** frac
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        E[i] = e1
        E[j] = e2
        c2 = _bad(N, D, E)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            cost = c2
        else:
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cost == 0


def _splice(N, d, E, rng):
    """Insert one new A-vertex (index N) and one new B-vertex (index N) into a d-regular graph.

    Pick d edges (a_i, b_i) with distinct a_i and distinct b_i; remove them and add
    (a_i, N) and (N, b_i). Every degree stays d. Returns (N + 1, new edge list) or None.
    """
    idx = list(range(len(E)))
    rng.shuffle(idx)
    ua, ub, pick = set(), set(), []
    for i in idx:
        a, b = E[i]
        if a in ua or b in ub:
            continue
        pick.append(i)
        ua.add(a)
        ub.add(b)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    picked = set(pick)
    NE = [E[i] for i in range(len(E)) if i not in picked]
    for i in pick:
        a, b = E[i]
        NE.append((N, b))
        NE.append((a, N))
    return N + 1, NE


def _grow(d, D, deadline, rng):
    """Grow a d-regular bipartite graph by edge splicing; return the largest valid (N, E) found."""
    N = d
    E = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}: valid for D >= 2
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        res = _splice(N, d, E, rng)
        if res is None:
            break
        N2, E2 = res
        S2 = set(E2)
        steps = 800 + 10 * N2
        if _repair(N2, D, E2, S2, rng, deadline, steps):
            N, E = N2, E2
            fails = 0
        else:
            fails += 1
    return N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} meets the Moore bound 2d

    moore = lib._moore_bound(d, D)
    best = lib.haar_graph(d, range(d))

    # Structured baseline for D = 3 (projective plane meets the bound when d-1 is a prime power).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if best[0] >= moore:
                return best

    # Edge-splice growth with annealed repair for every other case, and as a
    # general search for D = 3 when the projective plane is not regular enough.
    if best[0] < moore and d >= 2:
        N, E = _grow(d, D, deadline, rng)
        n = 2 * N
        edges = [(a, N + b) for a, b in E]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
