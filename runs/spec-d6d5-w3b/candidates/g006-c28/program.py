import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bit-parallel bad-pair counter for a general bipartite graph given by adjacency sets.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Ordered pairs at distance > D. Zero iff the graph has diameter <= D."""
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


# ----------------------------------------------------------------------------
# Degree-preserving edge switch. Edges are stored as (a, b) with a on side A, b on side B.
# Switch (i, j): (a,b),(c,e) -> (a,e),(c,b). Applying it twice restores the original.
# ----------------------------------------------------------------------------

def _switch(adj, E, i, j):
    a, b = E[i]
    c, e = E[j]
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)
    E[i] = (a, e)
    E[j] = (c, b)


# ----------------------------------------------------------------------------
# Main new family: grow a d-regular bipartite graph one A-B pair at a time.
# A new pair takes over d matching edges (x_t, y_t): x_t is joined to the new B
# vertex and y_t to the new A vertex, so all degrees stay exactly d. Then
# degree-preserving switches anneal the bad-pair count to zero.
# ----------------------------------------------------------------------------

def _grow_step(n, adj, E, d, D, rng, iters, deadline):
    """Try one pair extension of a valid d-regular graph. Returns (N, adj, E) or None."""
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    used_a, used_b, pick = set(), set(), []
    for idx in idxs:
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pick.append(idx)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None

    pset = set(pick)
    P = [E[idx] for idx in pick]
    N = n + 2
    na, nb = n, n + 1
    E2 = [e for idx, e in enumerate(E) if idx not in pset]
    adj2 = [set(s) for s in adj] + [set(), set()]
    for a, b in P:
        adj2[a].discard(b)
        adj2[b].discard(a)
        E2.append((na, b))
        E2.append((a, nb))
        adj2[na].add(b)
        adj2[b].add(na)
        adj2[a].add(nb)
        adj2[nb].add(a)

    cost = _bad_count(N, adj2, D)
    it = 0
    while cost and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(len(E2))
        j = rng.randrange(len(E2))
        a, b = E2[i]
        c, e = E2[j]
        if a == c or b == e or e in adj2[a] or b in adj2[c]:
            continue
        _switch(adj2, E2, i, j)
        new = _bad_count(N, adj2, D)
        if new <= cost or rng.random() < 0.02:
            cost = new
        else:
            _switch(adj2, E2, i, j)
    if cost == 0:
        return N, adj2, E2
    return None


def _grow(n, adj, E, d, D, deadline, rng, iters=60):
    """Repeatedly extend a valid d-regular graph; returns (n, edges) of the largest reached."""
    fails = 0
    while fails < 12 and time.monotonic() < deadline:
        r = _grow_step(n, adj, E, d, D, rng, iters, deadline)
        if r is None:
            fails += 1
        else:
            n, adj, E = r
            fails = 0
    return n, E


# ----------------------------------------------------------------------------
# Voltage lifts over small semidirect products (secondary family for D >= 5).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _lift_cost(k, G, D, darts, perms, limit):
    """Unreached (representative, vertex) pairs within distance D; zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a, base_b = i * G, (k + j) * G
        for g in range(G):
            a, b = base_a + g, base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        dist = [-1] * N
        dist[src] = 0
        frontier = [src]
        count = 1
        for step in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = step
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _lift_anneal(d, D, k, G, mul, rng, end, iters):
    """Anneal voltages and layer wiring; returns (n, edges) if valid, else None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms, float("inf"))
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > end:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            s = rng.randrange(G)
            if s == old_s:
                continue
            darts[idx][2] = s
            perms[idx] = [mul(g, s) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    end = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular with diameter 2 (valid for D >= 2).
    best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            return True
        return False

    # Projective plane incidence graph: d-regular with diameter 3 when d-1 is a prime power.
    if lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)

    # Every candidate in `best` is d-regular, so growth can always start from it.

    # Voltage-lift phase (used for D >= 5), first half of the budget.
    if D >= 5:
        lift_end = t0 + 0.5 * budget
        while time.monotonic() < lift_end:
            k = rng.choice([1, 1, 2, 3])
            lo = max(2, best[0] // (2 * k) + 1)
            G = rng.randint(lo, lo + max(3, lo // 8))
            g = _sample_group(G, rng)
            if g is None:
                continue
            res = _lift_anneal(d, D, k, g[0], g[1], rng, lift_end, 300)
            if res is not None:
                consider(res[0], res[1])

    # Pair growth from the best regular valid graph for the rest of the budget.
    n_b, e_b = best
    adj = [set() for _ in range(n_b)]
    for u, v in e_b:
        adj[u].add(v)
        adj[v].add(u)
    n_g, e_g = _grow(n_b, adj, list(e_b), d, D, end, rng)
    consider(n_g, e_g)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return best[0], list(best[1])
