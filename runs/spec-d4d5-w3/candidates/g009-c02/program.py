import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Regular bipartite graphs as edge sets on A = {0..m-1}, B = {0..m-1}.
# Every vertex has degree d. Growth inserts one A vertex and one B vertex by
# splicing d edges, which keeps the graph d-regular. A repair phase then uses
# 2-switches (degree-preserving, bipartiteness-preserving) with simulated
# annealing on the number of vertex pairs at distance more than D.
# ----------------------------------------------------------------------------

def _cost(m, E, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls). Zero means valid."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    for i, j in E:
        b = m + j
        adj[i].append(b)
        adj[b].append(i)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _repair(m, E, S, D, moves, deadline, rng):
    """Annealed 2-switch search for a zero-cost state. Mutates E and S in place."""
    c = _cost(m, E, D)
    L = len(E)
    for t in range(moves):
        if c == 0:
            return True
        if time.monotonic() > deadline:
            return False
        p = rng.randrange(L)
        q = rng.randrange(L)
        if p == q:
            continue
        a1, b1 = E[p]
        a2, b2 = E[q]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[p] = n1
        E[q] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        c2 = _cost(m, E, D)
        delta = c2 - c
        T = 0.8 * (0.04 ** (t / moves))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
        else:
            E[p] = (a1, b1)
            E[q] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
    return c == 0


def _pick_matching(E, d, rng):
    """Indices of d edges with pairwise distinct A-ends and distinct B-ends, or None."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_i, used_j, chosen = set(), set(), []
    for k in idx:
        i, j = E[k]
        if i in used_i or j in used_j:
            continue
        used_i.add(i)
        used_j.add(j)
        chosen.append(k)
        if len(chosen) == d:
            return chosen
    return None


def _search(d, D, deadline, rng):
    """Grow a d-regular bipartite graph one vertex pair at a time, repairing after each step.

    Returns (m, E) for the last state that was verified to have diameter <= D.
    """
    m = d
    E = [(i, j) for i in range(d) for j in range(d)]
    moves = 1500
    while time.monotonic() < deadline:
        pick = _pick_matching(E, d, rng)
        if pick is None:
            break
        chosen = set(pick)
        E2 = [e for k, e in enumerate(E) if k not in chosen]
        for k in pick:
            i, j = E[k]
            E2.append((m, j))   # new A vertex m joins old B vertex j
            E2.append((i, m))   # old A vertex i joins new B vertex m
        m2 = m + 1
        S2 = set(E2)
        if _repair(m2, E2, S2, D, moves, deadline, rng):
            m, E = m2, E2
            moves = 1500
        else:
            moves = min(int(moves * 1.2) + 1, 40000)
    return m, E


def _complete(d):
    """K_{d,d} as (n, edges): diameter 2, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return _complete(d)

    best = _complete(d)

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    try:
        m, E = _search(d, D, deadline, rng)
        if m > d:
            n, e = 2 * m, [(i, m + j) for i, j in E]
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _complete(d)
    return best
