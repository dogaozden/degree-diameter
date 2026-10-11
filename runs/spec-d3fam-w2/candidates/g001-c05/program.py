import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (diameter 3): projective plane incidence graphs and the
# Araujo-Pardo & Lopez family for d = q + 2.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: GROUP Haar graphs over non-abelian groups.
#
# For a finite group G of order N and a set S of d elements containing the
# identity, put a_g ~ b_{g s} for s in S. Then:
#   * a_g and a_h are at distance 2 iff h in g * S * S^{-1}, so same-side
#     distance <= 2 holds for all pairs iff S * S^{-1} = G (a "difference
#     cover" in the group);
#   * a_g and b_h are at distance <= 3 whenever S S^{-1} = G (because
#     g^{-1} h = s t^{-1} with 1 in S, giving a path of length 3).
# So diameter 3 holds with order 2N and degree d.
#
# The parent only searched cyclic groups. Here we search over ALL semidirect
# products Z_m x| Z_k (order N = m*k, several twists r) for each N, using
# simulated annealing to find the difference cover. Looping N upward from the
# current record half-order gives beats whenever some group of that order
# admits a cover.
# ----------------------------------------------------------------------------

def _candidate_groups(N, rng, cap=24):
    """Cyclic group plus semidirect products Z_m x| Z_k with m*k = N, shuffled and capped."""
    cands = [lib.cyclic_group(N)]
    extra = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    extra.append(lib.semidirect_group(m, k, r))
                except ValueError:
                    pass
    rng.shuffle(extra)
    cands.extend(extra[: max(0, cap - 1)])
    return cands


def _group_tables(order, mul, inv):
    """Multiplication table T[x][y] and inverse list I for a group on 0..order-1 (identity 0)."""
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return T, I


def _cover_cost(S, T, I, N):
    """Number of group elements not in S * S^{-1}."""
    cnt = [0] * N
    for s in S:
        Ts = T[s]
        for t in S:
            cnt[Ts[I[t]]] += 1
    return cnt.count(0)


def _group_anneal(d, N, T, I, rng, deadline):
    """Find S (|S| = d, identity in S) with S * S^{-1} = G; None on timeout."""
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _cover_cost(S, T, I, N)
    if cost == 0:
        return S
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    it = 0
    temp = 0.7
    while True:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
            temp = 0.7 * (0.03 ** frac)
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        S[idx] = x
        c = _cover_cost(S, T, I, N)
        if c <= cost or rng.random() < math.exp(-(c - cost) / temp):
            cost = c
            if cost == 0:
                return list(S)
        else:
            S[idx] = old


def _search_order(d, N, rng, deadline):
    """Try to find a group of order N with a degree-d difference cover; return (2N, edges) or None."""
    cands = _candidate_groups(N, rng)
    tables = [None] * len(cands)
    pool_end = min(deadline, time.monotonic() + max(2.0, 0.35 * (deadline - time.monotonic())))
    while time.monotonic() < pool_end:
        order_idx = list(range(len(cands)))
        rng.shuffle(order_idx)
        for gi in order_idx:
            now = time.monotonic()
            slice_t = min(0.6, pool_end - now)
            if slice_t <= 0:
                break
            if tables[gi] is None:
                _, mul, inv = cands[gi]
                tables[gi] = _group_tables(N, mul, inv)
            T, I = tables[gi]
            S = _group_anneal(d, N, T, I, rng, time.monotonic() + slice_t)
            if S is not None:
                edges = []
                for g in range(N):
                    Tg = T[g]
                    for s in S:
                        edges.append((g, N + Tg[s]))
                return 2 * N, edges
    return None


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
        # Known record families first.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # New search: group Haar graphs over semidirect products.
        # A success at order N gives 2N vertices, so start at the first N that beats best.
        if d >= 3:
            lo = max(d, best_n // 2 + 1)
            hi = d * (d - 1) + 1  # ordered differences d(d-1) must cover N - 1 elements
            N = lo
            while N <= hi and time.monotonic() < deadline:
                res = _search_order(d, N, rng, deadline)
                if res is None:
                    break
                consider(res[0], res[1])
                N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
