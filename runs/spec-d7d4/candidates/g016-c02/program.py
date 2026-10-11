import math
import random
import time

import lib


def _pg_base(d):
    """Incidence graph of PG(2, q) with q = d - 1 (or the largest smaller prime power): diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(S, mulT, invL, N, D):
    """Number of (source, target) pairs farther than D apart, for the Haar-type bi-Cayley graph
    with A-vertices x and B-vertices y, where a_x ~ b_{x*g} for g in S.

    The left translations are automorphisms that preserve each side, so pairs reduce to
    distances from a_e and from b_e. The graph has diameter <= D iff this cost is 0.
    """
    adjA = [[N + row[g] for g in S] for row in mulT]
    Sinv = [invL[g] for g in S]
    adjB = [[row[h] for h in Sinv] for row in mulT]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                nb = adjA[u] if u < N else adjB[u - N]
                for v in nb:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += 2 * N - cnt
    return total


def _groups(N, rng):
    """Candidate groups of order N: cyclic, plus a few semidirect products Z_m x| Z_k."""
    out = [lib.cyclic_group(N)]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append(lib.semidirect_group(m, k, r))
    rng.shuffle(out)
    return out[:6]


def _tables(order, mul, inv):
    mulT = [[mul(x, y) for y in range(order)] for x in range(order)]
    invL = [inv(x) for x in range(order)]
    return mulT, invL


def _anneal(mulT, invL, N, d, D, deadline, rng):
    """Search for d distinct shifts S with zero cost, by annealing with restarts."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = _cost(S, mulT, invL, N, D)
        best_c = cur
        stale = 0
        T = 0.6
        while cur > 0 and stale < 4000 and time.monotonic() < deadline:
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in S:
                stale += 1
                continue
            S2 = S[:]
            S2[i] = g
            c = _cost(S2, mulT, invL, N, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S, cur = S2, c
            if cur < best_c:
                best_c = cur
                stale = 0
            else:
                stale += 1
        if cur == 0:
            return S
    return None


def _try_order(N, d, D, deadline, rng):
    """Try to find a valid bi-Cayley graph with side order N; return (mulT, S) or None."""
    cands = _groups(N, rng)
    for idx, (order, mul, inv) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        sub = (deadline - now) / (len(cands) - idx)
        mulT, invL = _tables(order, mul, inv)
        S = _anneal(mulT, invL, N, d, D, now + sub, rng)
        if S is not None:
            return mulT, S
    return None


def _haar_edges(N, mulT, S):
    return [(x, N + mulT[x][g]) for x in range(N) for g in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Baseline: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound: nothing to gain.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # Bi-Cayley (Haar-type) search over groups of side order N, grown by ascending N.
    if d >= 2 and D >= 2:
        lo = None
        N = max(d, best[0] // 2 + 1)
        step = max(1, N // 16)
        while time.monotonic() < deadline and N >= d:
            res = None
            for _ in range(2):
                budget = min(deadline, time.monotonic() + max(1.0, 0.06 * time_limit))
                res = _try_order(N, d, D, budget, rng)
                if res is not None:
                    break
            if res is not None:
                mulT, S = res
                consider(2 * N, _haar_edges(N, mulT, S))
                lo = N
                N = lo + step
            else:
                if step == 1 or N <= d:
                    break
                step = 1
                N = lo + 1 if lo is not None else max(d, N - max(1, N // 8))

    return best
