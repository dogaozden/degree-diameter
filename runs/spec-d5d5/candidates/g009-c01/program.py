import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Edge-level growth and annealing for d-regular bipartite graphs.
#
# A graph is stored as m (side size) and E, a list of distinct pairs (a, b)
# with a, b in 0..m-1, meaning A-vertex a is joined to B-vertex b. Vertex
# labels in the output are A_a -> a and B_b -> m + b.
#
# Growth: adding one A-vertex and one B-vertex to a d-regular graph works like
# this. Choose d edges (a_k, b_k) with pairwise distinct a_k and distinct b_k.
# Replace each (a_k, b_k) by (a_k, new_B), and add (new_A, b_k). Every old
# degree is kept, and the two new vertices get degree d.
#
# Repair: 2-switch moves (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep the graph
# d-regular and bipartite. Simulated annealing minimises the number of vertex
# pairs farther apart than D. Distances are computed with bitmask balls.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 400
MAX_STEP = 16


def _adj_from_edges(m, E):
    nb = [[] for _ in range(2 * m)]
    for a, b in E:
        nb[a].append(m + b)
        nb[m + b].append(a)
    return nb


def _bad_pairs(n, nb, D):
    """Number of unordered vertex pairs at distance greater than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow_once(m, E, d, rng):
    """Add one A-vertex and one B-vertex to a d-regular graph. Returns (m+1, E2) or None."""
    for _ in range(30):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        usedA, usedB, chosen = set(), set(), []
        for k in idx:
            a, b = E[k]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            chosen.append(k)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            E2 = list(E)
            for k in chosen:
                a, b = E[k]
                E2[k] = (a, m)          # a stays, its partner becomes new B-vertex m
                E2.append((m, b))       # new A-vertex m takes over b
            return m + 1, E2
    return None


def _anneal(m, E, D, rng, deadline, iters):
    """2-switch simulated annealing on E (mutated in place). Returns (cost, E)."""
    eset = set(E)
    cost = _bad_pairs(2 * m, _adj_from_edges(m, E), D)
    L = len(E)
    T0, T1 = 1.5, 0.15
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _bad_pairs(2 * m, _adj_from_edges(m, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cost, E


def _to_edges(m, E):
    return [(a, m + b) for a, b in E]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def _build_inner(d, D, seed, time_limit, state):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    # Safe fallback: K_{d,d}, diameter 2.
    state["best"] = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    if D == 2 or state["best"][0] >= moore:
        return

    # Structured baseline: PG(2, d-1) incidence has diameter 3 and degree d.
    pg_start = None
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n2, pe = lib.projective_plane_incidence(d - 1)
        m0 = n2 // 2
        consider(n2, pe)
        if state["best"][0] >= moore:
            return
        pg_start = (m0, [(u, v - m0) for u, v in pe])

    if pg_start is not None:
        cur_m, cur_E = pg_start
    else:
        cur_m = d
        cur_E = [(a, b) for a in range(d) for b in range(d)]

    # Adaptive growth chain: grow by `step` vertex pairs, repair with annealing,
    # and keep the last fully valid state.
    step, iters, fails = 1, ANNEAL_ITERS, 0
    while time.monotonic() < deadline and 2 * cur_m < moore:
        cm, cE = cur_m, list(cur_E)
        okg = True
        for _ in range(step):
            r = _grow_once(cm, cE, d, rng)
            if r is None:
                okg = False
                break
            cm, cE = r
        if not okg or 2 * cm > moore:
            if step > 1:
                step //= 2
                continue
            break

        cost, cE = _anneal(cm, cE, D, rng, deadline, iters)
        if cost == 0:
            cur_m, cur_E = cm, cE
            step = min(step * 2, MAX_STEP)
            iters = ANNEAL_ITERS
            consider(2 * cur_m, _to_edges(cur_m, cur_E))
        else:
            if step > 1:
                step //= 2
            else:
                fails += 1
                iters = min(iters * 2, 4000)
                if fails >= 4:
                    break


def build(d, D, seed, time_limit):
    state = {"best": (1, [])}
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    try:
        _build_inner(d, D, seed, time_limit, state)
    except Exception:
        pass
    n, e = state["best"]
    if n > 1 and not lib.is_valid(n, e, d, D):
        return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]
    return n, e
