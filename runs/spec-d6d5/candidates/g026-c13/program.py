import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines: projective plane incidence graph and K_{d,d}.
# ----------------------------------------------------------------------------

def _pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, as (n, edges)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, edges = lib.projective_plane_incidence(q)
            return n, list(edges)
    return None


# ----------------------------------------------------------------------------
# Cost: number of unordered vertex pairs farther apart than D (bitmask balls).
# ----------------------------------------------------------------------------

def _cost_full(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW IDEA: matched-pair insertion with swap repair.
#
# Pick a matching M of d edges (a_i, b_i) (a_i on side A, b_i on side B). Delete
# them, add a new A-vertex v joined to all b_i and a new B-vertex u joined to all
# a_i. Every old vertex keeps its degree, v and u get degree d, and bipartiteness
# is preserved, so the order grows by exactly 2. The new pair is generally too
# far from the rest, so degree-preserving double-edge swaps (a,b),(c,e) ->
# (a,e),(c,b) anneal the cost back to zero. If annealing fails the state is
# discarded and the step is retried with a different matching.
# ----------------------------------------------------------------------------

def _swap_anneal(n, E, D, rng, deadline, iters):
    """Anneal degree-preserving swaps on bipartite edge list E (tuples (a, b), a on side A).

    Returns (cost, E) with cost 0 iff the graph has diameter <= D.
    """
    E = list(E)
    m = len(E)
    adj = [[] for _ in range(n)]
    keys = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        keys.add((a, b))
    cost = _cost_full(n, adj, D)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in keys or (c, b) in keys:
            continue
        adj[a].remove(b); adj[b].remove(a)
        adj[c].remove(e); adj[e].remove(c)
        adj[a].append(e); adj[e].append(a)
        adj[c].append(b); adj[b].append(c)
        c2 = _cost_full(n, adj, D)
        if c2 <= limit:
            keys.discard((a, b)); keys.discard((c, e))
            keys.add((a, e)); keys.add((c, b))
            E[i] = (a, e)
            E[j] = (c, b)
            cost = c2
        else:
            adj[a].remove(e); adj[e].remove(a)
            adj[c].remove(b); adj[b].remove(c)
            adj[a].append(b); adj[b].append(a)
            adj[c].append(e); adj[e].append(c)
    return cost, E


def _grow(n, E, d, D, moore, deadline, rng):
    """Repeatedly insert a matched pair of new vertices and repair by swaps. Returns (n, E), valid."""
    fails = 0
    while time.monotonic() < deadline and fails < 3 and n + 2 <= moore:
        used = set()
        M = []
        order = list(range(len(E)))
        rng.shuffle(order)
        for t in order:
            a, b = E[t]
            if a in used or b in used:
                continue
            used.add(a)
            used.add(b)
            M.append(t)
            if len(M) == d:
                break
        if len(M) < d:
            break
        Ms = set(M)
        v, u = n, n + 1
        E2 = [E[t] for t in range(len(E)) if t not in Ms]
        for t in M:
            a, b = E[t]
            E2.append((v, b))
            E2.append((a, u))
        slice_end = min(deadline, time.monotonic() + 4.0)
        cost, E3 = _swap_anneal(n + 2, E2, D, rng, slice_end, 1500)
        if cost == 0:
            n, E = n + 2, E3
            fails = 0
        else:
            fails += 1
    return n, E


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k2 (base: k vertices per side).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(60):
        k2 = rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [x for x in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
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


def _lift_cost(k, G, D, darts, perms, limit=float("inf")):
    """Unreached (representative, vertex) pairs over base representatives; zero iff valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
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
        if total > limit:
            return total
    return total


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            old_p = perms[idx]
            s = rng.randrange(G)
            darts[idx][2] = s
            perms[idx] = _right_perm(mul, G, s)
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
    return darts, perms, cost


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_phase(d, D, state, deadline, rng):
    """Search voltage lifts; return the largest valid (n, edges) state found."""
    best_n = state[0]
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 6)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        darts, perms, cost = _lift_anneal(d, D, k, order, mul, rng, deadline, 1200)
        if cost != 0:
            continue
        n, E = _lift_edges(k, order, darts, perms)
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n = n
            state = (n, E)
    return state


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    k_dd = lib.haar_graph(d, range(d))
    state = (k_dd[0], list(k_dd[1]))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal state
        if n > state[0] and lib.is_valid(n, e, d, D):
            state = (n, list(e))

    if D >= 3:
        pg = _pg_start(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        lift_deadline = min(deadline, start + 0.45 * time_limit)
        new_state = _lift_phase(d, D, state, lift_deadline, rng)
        consider(new_state[0], new_state[1])

    if D >= 3 and state[0] + 2 <= moore:
        n2, e2 = _grow(state[0], state[1], d, D, moore, deadline, rng)
        consider(n2, e2)

    n, e = state
    if not lib.is_valid(n, e, d, D):
        n, e = k_dd
    return n, e

