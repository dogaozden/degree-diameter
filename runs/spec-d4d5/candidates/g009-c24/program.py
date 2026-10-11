import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 1: annealed bi-Cayley voltage lifts over Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Family 2 (bold change): direct simulated annealing on d-regular bipartite
# graphs with double-edge switches. No group structure is imposed. The cost is
# the number of ordered vertex pairs at distance > D, computed with bitmasks.
# The search targets an order strictly above the current best.
# ----------------------------------------------------------------------------

def _bad_ordered(n, adjs, D):
    """Ordered pairs (v, w) with dist(v, w) > D, computed by bitmask ball growth."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjs[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _swap(E, Eset, adjs, i, j, n1, n2):
    """Replace edges E[i], E[j] by n1, n2, keeping Eset and adjacency sets in sync."""
    for a, b in (E[i], E[j]):
        Eset.discard((a, b))
        adjs[a].discard(b)
        adjs[b].discard(a)
    E[i] = n1
    E[j] = n2
    for a, b in (n1, n2):
        Eset.add((a, b))
        adjs[a].add(b)
        adjs[b].add(a)


def _regular_sa(d, D, s, rng, deadline):
    """Anneal a d-regular bipartite graph on sides of size s (A = 0..s-1, B = s..2s-1).

    Starts from the Haar graph with shifts 0..d-1 (requires s >= d) and applies
    double-edge switches. Returns the edge list (pairs (a, b) with b >= s) or None.
    """
    n = 2 * s
    E = [(a, s + (a + k) % s) for k in range(d) for a in range(s)]
    Eset = set(E)
    adjs = [set() for _ in range(n)]
    for a, b in E:
        adjs[a].add(b)
        adjs[b].add(a)
    cost = _bad_ordered(n, adjs, D)
    if cost == 0:
        return E
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        _swap(E, Eset, adjs, i, j, (a1, b2), (a2, b1))
        c2 = _bad_ordered(n, adjs, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(E, Eset, adjs, i, j, (a1, b1), (a2, b2))
    return E if cost == 0 else None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, max degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    if D == 3:
        return best

    # Phase 1: annealed group lifts (strongest family for D >= 5 so far).
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    anneal_iters = 1500 if D >= 5 else 400
    lift_deadline = start + 0.35 * time_limit
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < lift_deadline:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, lift_deadline, 120)
            if S is not None:
                consider(*lib.haar_graph(haar_m, S))
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=anneal_iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2 (bold): direct regular-bipartite annealing, targeting order best_n + 2.
    sa_deadline = start + 0.88 * time_limit
    while time.monotonic() < sa_deadline:
        s = best_n // 2 + 1
        if s < d:
            break
        before = best_n
        E = _regular_sa(d, D, s, rng, sa_deadline)
        if E is None:
            break
        consider(2 * s, E)
        if best_n == before:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
