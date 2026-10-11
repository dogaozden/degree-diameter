import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _half_ok(n, edges):
    """True if n is even and every edge joins 0..n/2-1 to n/2..n-1."""
    h = n // 2
    return n % 2 == 0 and all(min(u, v) < h <= max(u, v) for u, v in edges)


# ----------------------------------------------------------------------------
# NEW IDEA: pair insertion + 2-switch repair.
#
# Given a valid bipartite graph on A = 0..m-1, B = m..2m-1, insert one new A
# vertex and one new B vertex. Pick d edges (a_t, b_t) with pairwise distinct
# endpoints, remove them, and add (a_t, nb) and (na, b_t). Every old vertex keeps
# its degree, the two new vertices get degree exactly d, and the graph is still
# bipartite. The insertion usually breaks only a few distances. A degree-
# preserving 2-switch annealing (swap the B-ends of two edges) then repairs the
# diameter with a bad-pair objective. Success yields a valid graph with 2 more
# vertices, and we chain the process.
# ----------------------------------------------------------------------------

def _bad_adj(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _make_adj(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _swap(E, adj, i, j):
    """2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it twice restores the graph."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    adj[a1].append(b2)
    adj[b2].append(a1)
    adj[a2].append(b1)
    adj[b1].append(a2)
    E[i] = [a1, b2]
    E[j] = [a2, b1]


def _insert_pair(E, m, d, rng):
    """Insert a new A/B vertex pair into a valid graph (A = 0..m-1, B = m..2m-1). Returns (m+1, E2) or None."""
    if m < d:
        return None
    na, nb = m, 2 * m + 1
    F = [[a, b + 1 if b >= m else b] for a, b in E]
    pick = None
    for _ in range(60):
        order = list(range(len(F)))
        rng.shuffle(order)
        usedA, usedB, cand = set(), set(), []
        for t in order:
            a, b = F[t]
            if a not in usedA and b not in usedB:
                usedA.add(a)
                usedB.add(b)
                cand.append(t)
                if len(cand) == d:
                    break
        if len(cand) == d:
            pick = cand
            break
    if pick is None:
        return None
    for t in pick:
        a, b = F[t]
        F[t] = [a, nb]
        F.append([na, b])
    return m + 1, F


def _anneal_switch(n, E, D, rng, deadline):
    """Repair diameter by degree-preserving 2-switches with Metropolis acceptance. Returns E or None."""
    adj = _make_adj(n, E)
    L = len(E)
    cost = _bad_adj(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.5
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = max(0.05, 1.5 * (1.0 - (now - t0) / span))
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _swap(E, adj, i, j)
        c2 = _bad_adj(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(E, adj, i, j)
    return E if cost == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (annealed).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6])
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
    """Unreached (orbit representative, vertex) pairs. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T_end = 0.5
    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main construction.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    best_E = [[min(u, v), max(u, v)] for u, v in best[1]]

    def consider(n, e):
        nonlocal best, best_n, best_E
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            best_E = [[min(u, v), max(u, v)] for u, v in e] if _half_ok(n, e) else None

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D <= 2:
        return best

    lift_ok = D >= 5 and d >= 3
    while time.monotonic() < deadline and best_n < lib._moore_bound(d, D):
        now = time.monotonic()
        lim = min(deadline, now + max(2.0, 0.25 * (deadline - now)))
        m = best_n // 2
        can_grow = best_E is not None and m >= d

        if lift_ok and (not can_grow or rng.random() < 0.5):
            k = rng.choice([1, 2, 2, 3, 4])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lim, 300)
            if res is not None:
                consider(res[0], res[1])
        elif can_grow:
            ins = _insert_pair(best_E, m, d, rng)
            if ins is None:
                continue
            m2, E2 = ins
            res = _anneal_switch(2 * m2, E2, D, rng, lim)
            if res is not None:
                consider(2 * m2, [(a, b) for a, b in res])
        else:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
