import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence graph and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bitset reachability cost. Counts ordered pairs at distance > D (0 iff valid).
# ----------------------------------------------------------------------------

def _bad_pairs_adj(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# NEW ROUTINE: 2-switch annealing repair on a bipartite graph.
#
# Starting from an oversized near-miss graph (left/right sides given), it
# performs degree-preserving 2-switches (a,b),(c,e) -> (a,e),(c,b) and
# opportunistic edge insertions between deficient opposite-side vertices.
# Moves are Metropolis-accepted on the number of bad (distance > D) pairs.
# Bipartiteness and the degree bound are preserved by construction.
# ----------------------------------------------------------------------------

def _switch_anneal(n, edges, left, d, D, deadline, rng, T0=0.8):
    E = []
    for u, v in edges:
        E.append([u, v] if left[u] else [v, u])
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    if sum(len(s) for s in adj) != 2 * len(E):
        return None
    deg = [len(s) for s in adj]
    lefts = [v for v in range(n) if left[v]]
    rights = [v for v in range(n) if not left[v]]
    cost = _bad_pairs_adj(n, adj, D)
    T = T0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.3:
            la = [v for v in lefts if deg[v] < d]
            rb = [v for v in rights if deg[v] < d]
            if not la or not rb:
                continue
            a = rng.choice(la)
            b = rng.choice(rb)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            c2 = _bad_pairs_adj(n, adj, D)
            if c2 <= limit:
                cost = c2
                deg[a] += 1
                deg[b] += 1
                E.append([a, b])
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            if len(E) < 2:
                continue
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(e)
            adj[e].add(a)
            adj[c].add(b)
            adj[b].add(c)
            c2 = _bad_pairs_adj(n, adj, D)
            if c2 <= limit:
                cost = c2
                E[i] = [a, e]
                E[j] = [c, b]
            else:
                adj[a].discard(e)
                adj[e].discard(a)
                adj[c].discard(b)
                adj[b].discard(c)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)
    if cost != 0:
        return None
    return n, [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# Each layer L holds one dart per i, with B-targets a permutation.
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice(k2_choices)
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


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _lift_adj(k, G, darts, perms):
    N = 2 * k * G
    adj = [set() for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].add(b)
            adj[b].add(a)
    return adj


def _lift_cost(D, k, G, darts, perms):
    return _bad_pairs_adj(2 * k * G, _lift_adj(k, G, darts, perms), D)


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Annealed search over voltages and layer B-assignments.

    Returns (edges_or_None, darts, perms, cost).
    """
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(D, k, G, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            old_p = perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _lift_cost(D, k, G, darts, perms)
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
            c2 = _lift_cost(D, k, G, darts, perms)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _lift_edges(k, G, darts, perms)[1], darts, perms, 0
    return None, darts, perms, cost


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Voltage-lift search with switch-annealing repair of near misses.
    ks = [1, 1, 1, 2, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    fallback_pool = [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 4)
        G = rng.randint(lo, hi)
        g = None
        if rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng, fallback_pool)
        if g is None:
            continue
        order, mul = g

        iters = 1200 if k == 1 else 400
        res, darts, perms, c = _anneal(d, D, k, order, mul, rng, deadline, iters)
        if res is not None:
            consider(2 * k * order, res)
            continue

        # Near miss: repair the full oversized lift by 2-switch annealing.
        if c <= 40 and time.monotonic() < deadline:
            N, E = _lift_edges(k, order, darts, perms)
            left = [v < k * order for v in range(N)]
            sw_deadline = min(deadline, time.monotonic() + 8.0)
            out = _switch_anneal(N, E, left, d, D, sw_deadline, rng)
            if out is not None:
                consider(out[0], out[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
