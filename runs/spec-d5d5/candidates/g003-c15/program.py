import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: simulated annealing over d-regular bipartite graphs.
#
# State: k vertices per side, edge list E of pairs (a, b) with a, b in 0..k-1,
# every vertex of degree d. Moves are double-edge swaps, which keep the graph
# simple and regular. The cost is the number of ordered vertex pairs at
# distance > D. Size grows by one vertex per side whenever cost reaches zero:
# d edges are removed and rewired to the two new vertices, which keeps the
# graph d-regular and simple.
# ----------------------------------------------------------------------------

def _bad_pairs(k, E, D):
    n = 2 * k
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(k + b)
        adj[k + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - bin(r).count("1") for r in reach)


def _random_regular(k, d, rng):
    """Random simple d-regular bipartite graph on k + k vertices as (E, S), or None."""
    for _ in range(200):
        E = []
        S = set()
        ok = True
        for _layer in range(d):
            found = False
            for _attempt in range(200):
                perm = list(range(k))
                rng.shuffle(perm)
                if all((a, perm[a]) not in S for a in range(k)):
                    found = True
                    break
            if not found:
                ok = False
                break
            for a in range(k):
                E.append([a, perm[a]])
                S.add((a, perm[a]))
        if ok:
            return E, S
    return None


def _grow(k, d, E, S, rng):
    """Add one A vertex and one B vertex, keeping the graph simple and d-regular."""
    pick = []
    for _ in range(100):
        order = list(range(len(E)))
        rng.shuffle(order)
        usedA, usedB = set(), set()
        pick = []
        for idx in order:
            a, b = E[idx]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            pick.append(idx)
            if len(pick) == d:
                break
        if len(pick) == d:
            break
    if len(pick) != d:
        return None
    ps = set(pick)
    newE, newS = [], set()
    for i, (a, b) in enumerate(E):
        if i in ps:
            continue
        newE.append([a, b])
        newS.add((a, b))
    na = k
    nb = k
    for idx in pick:
        a, b = E[idx]
        newE.append([a, nb])
        newE.append([na, b])
        newS.add((a, nb))
        newS.add((na, b))
    return k + 1, newE, newS


def _anneal(k, D, E, S, rng, deadline):
    """Anneal double-edge swaps until cost is zero or time runs out. Returns True on success."""
    cost = _bad_pairs(k, E, D)
    step = 0
    while cost > 0 and time.monotonic() < deadline:
        step += 1
        T = 0.4 + 3.0 * (0.98 ** (step % 400))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        c2 = _bad_pairs(k, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
    return cost == 0


# ----------------------------------------------------------------------------
# Secondary hedge: group-voltage lifts over semidirect products Z_m x| Z_k2.
# Kept as a fallback so the earlier record-level search is not lost.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups_of_order(G, rng, cap=40):
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:cap]:
            out.append((m, k2, r))
    return out


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _vcost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _vtrial(d, D, k, G, rng, iters, deadline, groups):
    if not groups:
        return None
    m, k2, r = rng.choice(groups)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(order)])
    perms = [_right_perm(mul, order, s) for _, _, s in darts]
    cost = _vcost(k, order, D, darts, perms)
    stall = 0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline or stall > 250:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(order)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, order, new_s)
        c2 = _vcost(k, order, D, darts, perms)
        stall = 0 if c2 < cost else stall + 1
        if c2 <= cost or rng.random() < 0.02:
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm
    if cost == 0:
        return _vedges(k, order, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = min(0.85 * time_limit, time_limit - 4.0)
    deadline = start + max(span, 0.5)
    sa_deadline = start + 0.7 * max(span, 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing to search for.
    if best_n >= lib._moore_bound(d, D):
        return best

    # Phase 1: annealing with incremental growth.
    k = max(d, 16)
    init = _random_regular(k, d, rng)
    if init is not None:
        E, S = init
        while time.monotonic() < sa_deadline:
            ok = _anneal(k, D, E, S, rng, sa_deadline)
            if not ok:
                break
            consider(2 * k, [(a, k + b) for a, b in E])
            g = _grow(k, d, E, S, rng)
            if g is None:
                break
            k, E, S = g

    # Phase 2: voltage-lift hedge for the remaining time.
    group_cache = {}

    def groups_for(G):
        if G not in group_cache:
            group_cache[G] = _groups_of_order(G, rng)
        return group_cache[G]

    while time.monotonic() < deadline:
        kk = 1 if rng.random() < 0.75 else rng.choice([2, 3])
        base = best_n // (2 * kk)
        spn = max(3, base // 8)
        G = max(2, base + 1 + rng.randrange(0, spn + 1))
        res = _vtrial(d, D, kk, G, rng, 800, deadline, groups_for(G))
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
