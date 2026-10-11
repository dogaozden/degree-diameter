import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Representation: a balanced bipartite graph with m left and m right vertices is
# a list E of pairs (a, b), a in 0..m-1 (left), b in 0..m-1 (right). Global
# labels are a for left and m + b for right.
#
# Construction: start from a small d-regular bipartite graph (projective plane
# incidence when d-1 is a prime power, else K_{d,d}). Repeatedly splice in one
# new left and one new right vertex of degree d, which keeps every old degree
# fixed. Then repair diameter violations with degree-preserving 2-switch
# simulated annealing on the count of pairs at distance > D.
# ----------------------------------------------------------------------------


def _to_global(m, E):
    return [(a, m + b) for a, b in E]


def _pg_start(d):
    """Projective plane incidence of PG(2, q) with q the largest prime power <= min(d-1, 11)."""
    for q in range(min(d - 1, 11), 1, -1):
        if lib.is_prime_power(q):
            n2, edges = lib.projective_plane_incidence(q)
            m = n2 // 2
            return m, [(u, v - m) for u, v in edges]
    return None


def _cost(m, E, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in E:
        bb = m + b
        adj[a].append(bb)
        adj[bb].append(a)
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
    return sum(n - r.bit_count() for r in reach)


def _splice(m, E, d, rng):
    """Add a left vertex m and a right vertex m, each of degree d, without changing any old degree."""
    k = len(E)
    if k < d:
        return None
    used, xs, ys, chosen = set(), set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 20000:
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
    x = m  # new left vertex
    y = m  # new right vertex
    for i in chosen:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    return m + 1, newE


def _anneal(m, E, D, deadline, rng, T0=1.0):
    """2-switch annealing toward diameter <= D. Returns the edge list on success, else None."""
    E = list(E)
    k = len(E)
    eset = set(E)
    cur = _cost(m, E, D)
    if cur == 0:
        return E
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.05, T0 * (1.0 - (now - t0) / span))
        i = rng.randrange(k)
        j = rng.randrange(k)
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
        new = _cost(m, E, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
            if cur == 0:
                return E
        else:
            E[i] = (a, b)
            E[j] = (c, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Starting point for the growth chain.
    pg = _pg_start(d) if D >= 3 else None
    if pg is not None:
        m, E = pg
        consider(2 * m, _to_global(m, E))
    else:
        m = d
        E = [(a, b) for a in range(d) for b in range(d)]

    # Growth chain: splice two vertices, then repair with annealing.
    cur_m, cur_E = m, E
    fails = 0
    budget = max(0.3, min(3.0, 0.02 * time_limit))
    while time.monotonic() < deadline - 0.2 and fails < 60:
        res = _splice(cur_m, cur_E, d, rng)
        if res is None:
            break
        m2, E2 = res
        if _cost(m2, E2, D) == 0:
            E3 = E2
        else:
            left = deadline - time.monotonic()
            if left <= 0.05:
                break
            E3 = _anneal(m2, E2, D, time.monotonic() + min(budget, left), rng)
        if E3 is None:
            fails += 1
            continue
        fails = 0
        cur_m, cur_E = m2, E3
        consider(2 * m2, _to_global(m2, E3))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
