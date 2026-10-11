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
# Shared bitset distance helpers.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bad_count(n, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D (twice the unordered count)."""
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball)


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (annealed).
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D."""
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
        if total > limit:
            return total
    return total


def _lift_edges(k, G, darts, perms):
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

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_search(d, D, rng, deadline, consider, get_n):
    """Repeatedly sample groups and anneal lifts sized just above the current best."""
    ks = [1, 1, 1, 2, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = get_n() // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(3, lo // 4)
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        iters = 1200 if k == 1 else 400
        res, _, _ = _anneal(d, D, k, order, mul, rng, deadline, iters)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# NEW: switch-annealing on plain d-regular bipartite graphs.
#
# Start from a random layered bipartite graph (d random perfect matchings
# between sides of size S). A "switch" replaces edges (a1,b1),(a2,b2) by
# (a1,b2),(a2,b1): degrees and bipartiteness are preserved. Metropolis
# annealing minimises the number of vertex pairs at distance > D. Sizes are
# tried from largest to smallest, so the first success is the best found.
# ----------------------------------------------------------------------------

def _switch_anneal(d, D, S, rng, deadline):
    """Try to find a bipartite graph with sides of size S, max degree d, diameter <= D."""
    N = 2 * S
    present = set()
    E = []
    for _ in range(d):
        pairs = []
        for _t in range(30):
            p = list(range(S))
            rng.shuffle(p)
            pairs = [(a, S + p[a]) for a in range(S)]
            if not any(e in present for e in pairs):
                break
        for e in pairs:
            if e not in present:
                present.add(e)
                E.append(e)

    cost = _bad_count(N, _adj_lists(N, E), D)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in present or n2 in present:
            continue
        E[i] = n1
        E[j] = n2
        present.discard((a1, b1))
        present.discard((a2, b2))
        present.add(n1)
        present.add(n2)
        c2 = _bad_count(N, _adj_lists(N, E), D)
        T = max(0.2, T * 0.999)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            present.discard(n1)
            present.discard(n2)
            present.add((a1, b1))
            present.add((a2, b2))
    return E if cost == 0 else None


def _switch_search(d, D, sizes, deadline, rng):
    """Attempt side sizes in the given order; return (n, edges) for the first success."""
    for idx, S in enumerate(sizes):
        now = time.monotonic()
        if now >= deadline:
            break
        budget = (deadline - now) * 0.45
        E = _switch_anneal(d, D, S, rng, now + budget)
        if E is not None:
            return 2 * S, list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit - 1.0
    deadline = start + max(0.5, total)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    holder = [fb_n, fb_e]

    def consider(n, e):
        if n > holder[0] and lib.is_valid(n, e, d, D):
            holder[0] = n
            holder[1] = e

    def get_n():
        return holder[0]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 5:
        # Phase 1: voltage lifts over small semidirect groups.
        lift_end = start + 0.4 * total
        _lift_search(d, D, rng, lift_end, consider, get_n)

        # Phase 2: switch-annealing above the current best, descending sizes.
        top = holder[0] // 2 + 35
        floor_s = holder[0] // 2 + 1
        sizes = list(range(top, floor_s - 1, -4))
        if sizes:
            found = _switch_search(d, D, sizes, deadline, rng)
            if found is not None:
                consider(found[0], found[1])

    n, e = holder
    if not lib.is_valid(n, e, d, D):
        n, e = fb_n, fb_e
    return n, list(e)
