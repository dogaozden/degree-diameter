import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base family: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Layers: A_i (i < k) and B_j (j < k). Vertex (layer, g) has id layer*G + g.
# For each colour L in range(d), layer i is matched to layer p_L(i) and the
# dart (i, p_L(i), s_L) joins A_{i,g} to B_{p_L(i), g*s_L} for all g.
# This gives every vertex degree exactly d.
#
# Left multiplication by a group element is an automorphism of the lift, so
# distances need to be measured from one representative per layer only.
#
# Distance-bounded reachability is evaluated with big-int bitsets: ball[v] is
# the set of vertices within radius t of v, updated for t = 1..D. The cost is
# the number of (representative, vertex) pairs at distance > D. Zero is valid.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(60):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
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


def _build_adj(k, G, darts, perms):
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
    return N, adj


def _cost(k, G, D, darts, perms):
    """Number of (layer representative, vertex) pairs not within distance D; 0 means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N, adj = _build_adj(k, G, darts, perms)
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    total = 0
    for layer in range(2 * k):
        total += N - ball[layer * G].bit_count()
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, t_end):
    """Time-scheduled simulated annealing over voltages and layer matchings."""
    darts = None
    perms = None
    cost = _BIG
    for _ in range(200):
        darts = []
        for _c in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
        perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
        cost = _cost(k, G, D, darts, perms)
        if cost < _BIG:
            break
    if cost >= _BIG:
        return None

    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    T0 = max(2.0, 0.1 * cost)
    T_end = 0.2

    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t0) / span
        T = T0 * (T_end / T0) ** frac

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
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
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0:
        return 1, []
    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    bound = lib._moore_bound(d, D)
    if D == 2 or best_n >= bound:
        return best if lib.is_valid(best[0], best[1], d, D) else fallback

    # Main search: bi-Cayley lifts aimed strictly above the current best order.
    # Each accepted lift raises the target, so the search climbs.
    while time.monotonic() < deadline and best_n < bound:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        seg = min(remaining, max(4.0, min(12.0, remaining * 0.3)))

        k = rng.choice([1, 1, 2, 2, 3, 3, 4, 5])
        G = best_n // (2 * k) + 1 + rng.randrange(0, 3)
        G = max(2, G)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, now + seg)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
