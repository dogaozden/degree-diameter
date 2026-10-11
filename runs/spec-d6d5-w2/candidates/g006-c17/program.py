import math
import random
import time

import lib

# New family for the weakest target (d=6, D=5): Haar graphs H(G, S) over
# non-abelian semidirect products G = Z_m x| Z_k. Vertices are A_x = x and
# B_z = G + z, and A_x ~ B_{x*s} for s in S with |S| = d. Left translation is a
# regular action on each side, so diameter <= D only needs checking from A_e and
# B_e. Each candidate is found by tabu-style annealing over S. The search climbs
# the group order upward from a high starting guess. Early exits, PG/Araujo
# baselines for D = 3, and K_{d,d} as a fallback keep every output valid.

_GROUP_CACHE = {}


def _groups(G):
    """All semidirect products Z_m x| Z_k of order G (m >= 2), as (m, k, r) triples."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    res = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                res.append((m, k, r))
    _GROUP_CACHE[G] = res
    return res


def _try_group(d, D, G, mul, inv, rng, deadline, iters):
    """Search an S (size d, containing identity 0) with no unreached pairs from A_e and B_e."""
    colR, colL = {}, {}

    def cols(s):
        if s not in colR:
            colR[s] = [mul(x, s) for x in range(G)]
            si = inv(s)
            colL[s] = [mul(z, si) for z in range(G)]
        return colR[s], colL[s]

    N = 2 * G

    def cost(S):
        cs = [cols(s) for s in S]
        adj = [None] * N
        for x in range(G):
            adj[x] = [G + cr[x] for cr, _ in cs]
        for z in range(G):
            adj[G + z] = [cl[z] for _, cl in cs]
        total = 0
        for src in (0, G):
            seen = bytearray(N)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    for v in adj[u]:
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                if not nxt:
                    break
                cnt += len(nxt)
                frontier = nxt
            total += N - cnt
        return total

    if G - 1 < d - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = cost(S)
    T = 2.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        best_t, best_c = None, None
        for _ in range(3):
            t = rng.randrange(1, G)
            if t in S:
                continue
            T2 = S[:]
            T2[i] = t
            c2 = cost(T2)
            if best_c is None or c2 < best_c:
                best_c, best_t = c2, t
        if best_t is None:
            continue
        if best_c <= c or rng.random() < math.exp(-(best_c - c) / T):
            S[i] = best_t
            c = best_c
        T = max(0.2, T * 0.99)
    return S if c == 0 else None


def _best_pg(d):
    """PG(2, q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.82 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= moore:
        return best_n, best_e

    # D = 3 baselines (instant).
    if D == 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass
        if best_n >= moore:
            return best_n, best_e

    # Main phase: Haar graphs over semidirect products, climbing the group order.
    if d >= 2:
        per_try = max(1.5, budget / 10.0)
        target = max(best_n // 2 + 1, d + 1, int(0.2 * moore))
        fails = 0
        while time.monotonic() < deadline - 0.3:
            if 2 * target > moore:
                target = best_n // 2 + 1
                if 2 * target > moore:
                    break
            groups = _groups(target)
            if not groups:
                target += 1
                continue
            m, k, r = rng.choice(groups)
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                target += 1
                continue
            try_deadline = min(deadline, time.monotonic() + per_try)
            S = _try_group(d, D, order, mul, inv, rng, try_deadline, 300)
            if S is not None:
                edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
                consider(2 * order, edges)
                target = best_n // 2 + 1
                fails = 0
            else:
                fails += 1
                if fails >= 6 and target > best_n // 2 + 1:
                    target -= 1
                    fails = 0

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
