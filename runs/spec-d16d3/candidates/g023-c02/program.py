import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _random_group(m, rng):
    """Return (a, k, r) describing Z_a x| Z_k of order m; cyclic (k=1) when no twisted option is found."""
    divs = [k for k in range(2, m) if m % k == 0 and m // k >= 2]
    if divs and rng.random() < 0.6:
        k = rng.choice(divs)
        a = m // k
        cands = [r for r in range(2, a)
                 if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a]
        if cands:
            return a, k, rng.choice(cands)
    return m, 1, 1


def _tables(a, k, r):
    """Multiplication table M[x][y] and difference table Dt[x][y] = x * y^{-1} of the group."""
    order, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    Dt = [[M[x][I[y]] for y in range(order)] for x in range(order)]
    return order, M, Dt


def _anneal(m, d, M, Dt, rng, deadline):
    """Find a d-subset S of a group of order m with S S^{-1} = G (identity excluded from the cover).

    Cost = number of non-identity group elements not written as s t^{-1} with s != t in S.
    Zero cost gives a Haar-type bipartite graph of diameter 3 on 2m vertices.
    Returns S, or None if the deadline passes first.
    """
    S = rng.sample(range(m), d)
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[Dt[S[i]][S[j]]] += 1
    cost = sum(1 for x in range(1, m) if cnt[x] == 0)
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if it & 255 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            T = 1.0 * (0.08 ** ((now - t_begin) / span))
        if rng.random() < 0.5:
            unc = [x for x in range(1, m) if cnt[x] == 0]
            x = rng.choice(unc)
            i = rng.randrange(d)
            j = rng.randrange(d)
            if i == j:
                continue
            new = M[x][S[j]]  # new * S[j]^{-1} = x
        else:
            i = rng.randrange(d)
            new = rng.randrange(m)
        old = S[i]
        if new == old or new in S:
            continue
        rem = []
        add = []
        for j in range(d):
            if j == i:
                continue
            s = S[j]
            rem.append(Dt[old][s])
            rem.append(Dt[s][old])
            add.append(Dt[new][s])
            add.append(Dt[s][new])
        delta = 0
        for x in rem:
            cnt[x] -= 1
            if cnt[x] == 0 and x != 0:
                delta += 1
        for x in add:
            if cnt[x] == 0 and x != 0:
                delta -= 1
            cnt[x] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = new
            cost += delta
        else:
            for x in add:
                cnt[x] -= 1
            for x in rem:
                cnt[x] += 1
    return S


def _haar_search(d, rng, deadline):
    """Search for the largest m such that a covering d-set exists in some group of order m.

    Returns (n, edges) of the best valid Haar-type graph found, or None.
    Vertices: A_g = g, B_h = m + h, edge A_g -- B_{g s} for s in S.
    """
    lo = max(d, 2)
    hi = d * (d - 1) + 1  # Moore-type bound on m for diameter 3
    best = None
    m = lo
    while m <= hi and time.monotonic() < deadline:
        S = None
        M = None
        while S is None and time.monotonic() < deadline:
            a, k, r = _random_group(m, rng)
            order, M, Dt = _tables(a, k, r)
            sub = min(deadline, time.monotonic() + 3.0)
            S = _anneal(order, d, M, Dt, rng, sub)
        if S is None:
            break
        edges = [(g, m + M[g][s]) for g in range(m) for s in S]
        n = 2 * m
        if lib.is_valid(n, edges, d, 3):
            best = (n, edges)
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, min(0.8 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3:
        # Main family: Haar graphs over (non-abelian) groups of order m whose
        # connection set S satisfies S S^{-1} = G; these have diameter 3 and
        # order 2m with m <= d(d-1)+1.
        res = _haar_search(d, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    return best_n, best_e
