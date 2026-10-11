import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: for D >= 3 the main search is now a bi-Cayley ("Haar-type")
# search over arbitrary finite groups of a chosen order G. The graph has
# vertices A_g = g and B_h = G + h, and the dart set S (|S| = d, distinct)
# gives edges A_g ~ B_{g*s} for s in S. Left multiplication is an automorphism,
# so distances only need checking from A_e and B_e.
#
# Groups are semidirect products Z_m x| Z_k (lib.semidirect_group), which
# include the cyclic group (k=1), direct products (r=1), and Frobenius groups
# such as Z_19 x| Z_18 of order 342, the group behind the 684-vertex record.
# Each group gets a simulated-annealing search over S. The target order climbs
# a ladder: each success raises the best order, so the next G is larger.
# ----------------------------------------------------------------------------


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of order G, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    rng.shuffle(divs)
    for k in divs[:12]:
        m = G // k
        if k == 1:
            r = 1
        else:
            cands = [1]
            pool = rng.sample(range(1, m), min(m - 1, 80))
            for r2 in pool:
                if math.gcd(r2, m) == 1 and pow(r2, k, m) == 1 % m:
                    cands.append(r2)
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul
    return None


def _ball_cost(G, D, pl):
    """Unreached (vertex, rep) pairs for reps A_e and B_e. pl is a list of (perm, invperm)."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for p, _ in pl:
                        v = G + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for _, ip in pl:
                        v = ip[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _haar_edges(G, pl):
    E = []
    for p, _ in pl:
        for g in range(G):
            E.append((g, G + p[g]))
    return 2 * G, E


def _search_group(d, D, order, mul, rng, deadline, iters):
    """Anneal a d-element dart set S in the group. Returns (n, edges) on success, else None."""
    cache = {}

    def get(s):
        if s not in cache:
            p = [mul(g, s) for g in range(order)]
            ip = [0] * order
            for g, x in enumerate(p):
                ip[x] = g
            cache[s] = (p, ip)
        return cache[s]

    S = rng.sample(range(order), d)
    cost = _ball_cost(order, D, [get(s) for s in S])
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        limit = cost - T * math.log(1.0 - rng.random())
        i = rng.randrange(d)
        x = rng.randrange(order)
        if x in S:
            continue
        newS = list(S)
        newS[i] = x
        c2 = _ball_cost(order, D, [get(s) for s in newS])
        if c2 <= limit:
            S, cost = newS, c2
    if cost == 0:
        return _haar_edges(order, [get(s) for s in S])
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # Projective plane incidence graph: diameter 3, degree q+1 for q = d-1.
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        n, e = lib.projective_plane_incidence(q)
        consider(n, e)

    # Araujo-Pardo-Lopez record for D = 3, degree q+2.
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    if D < 3:
        return best_n, best_e

    # Bi-Cayley search over semidirect products, with a ladder of target orders.
    side_bound = lib.moore_bound(d, D) // 2
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        if lo > side_bound:
            break
        if rng.random() < 0.5:
            G = lo + rng.randint(0, 6)
        else:
            G = lo + rng.randint(0, max(6, lo // 4))
        G = min(max(G, 2), side_bound)
        if G < d:
            continue
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _search_group(d, D, order, mul, rng, deadline, 500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
