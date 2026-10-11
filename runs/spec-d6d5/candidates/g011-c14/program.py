import math
import random
import time

import lib


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
# Bi-Cayley covering search.
#
# Group G (order g) with connection set S of size d. Vertices (x,0) and (y,1),
# with (x,0) ~ (y,1) iff x^-1 y in S. Left multiplication is an automorphism
# group acting transitively on each side, so the diameter is <= D iff
#   B^floor(D/2) = G                  (same-side distances)
#   B^floor((D-1)/2) * S = G          (cross-side distances)
# where B = S S^-1 (which contains the identity).
# ----------------------------------------------------------------------------

def _group_pool(g, rng):
    """Semidirect products Z_m x| Z_k of order g; nonabelian ones first."""
    pool = []
    for k in range(1, g + 1):
        if g % k:
            continue
        m = g // k
        if m < 2:
            continue
        if k == 1:
            rs = [1]
        else:
            cands = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(cands)
            rs = cands[:4]
        for r in rs:
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            pool.append((order, mul, inv, k > 1))
    rng.shuffle(pool)
    pool.sort(key=lambda t: 0 if t[3] else 1)
    return pool


def _cover_cost(G, mul, inv, S, D):
    """Number of uncovered group elements over both sides. Zero iff diameter <= D."""
    Sinv = [inv(s) for s in S]
    B = list({mul(s, t) for s in S for t in Sinv})
    t0 = D // 2
    t1 = (D - 1) // 2
    powers = [{0}]
    for _ in range(t0):
        prev = powers[-1]
        powers.append({mul(x, y) for x in prev for y in B})
    side0 = G - len(powers[t0])
    Q = {mul(x, s) for x in powers[t1] for s in S}
    side1 = G - len(Q)
    return side0 + side1


def _anneal(G, mul, inv, d, D, rng, deadline, iters):
    """Anneal a d-element connection set S by single-element replacements."""
    S = rng.sample(range(G), d)
    c = _cover_cost(G, mul, inv, S, D)
    T = 2.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cover_cost(G, mul, inv, S2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.998)
    return (S if c == 0 else None), c


def _bicayley_graph(G, mul, S):
    """Vertices 0..G-1 on side 0, G..2G-1 on side 1; (g,0) ~ (g*s,1)."""
    edges = [(g, G + mul(g, s)) for g in range(G) for s in S]
    return 2 * G, edges


def _bicayley_search(d, D, G, deadline, rng, consider):
    per_G = 1.5
    while time.monotonic() < deadline:
        if G <= d:
            G = d + 1
        pool = _group_pool(G, rng)
        budget_end = min(deadline, time.monotonic() + per_G)
        found = None
        for _order, mul, inv, _nonab in pool[:4]:
            if time.monotonic() >= budget_end:
                break
            S, _c = _anneal(G, mul, inv, d, D, rng, budget_end, 800)
            if S is not None:
                found = (mul, S)
                break
        if found is not None:
            n, e = _bicayley_graph(G, found[0], found[1])
            consider(n, e)
        G += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 4 and d >= 2:
        half_moore = lib._moore_bound(d, D) // 2
        G0 = max(best_n // 2 + 1, int(0.40 * half_moore), d + 1)
        _bicayley_search(d, D, G0, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
