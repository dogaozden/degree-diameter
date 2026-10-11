import math
import random
import time

import lib


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} for D >= 2, otherwise K_2."""
    if d < 1:
        return 1, []
    if D >= 2:
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    n, e = lib.haar_graph(1, [0])
    if lib.is_valid(n, e, d, D):
        return n, e
    return 1, []


def _group_candidates(N, rng):
    """(m, k, r) triples with m*k == N: cyclic Z_N plus semidirect Z_m x| Z_k."""
    out = []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if k == 1:
            out.append((m, 1, 1))
            continue
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 6:
            rs = rng.sample(rs, 6)
        for r in rs:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _hill(N, mul, inv, d, D, rng, t_end):
    """Hill-climb a connection set S (size d) in a group of order N so that the
    bipartite lift with darts (0,1,g), g in S, has diameter <= D.

    Left multiplication is an automorphism, so the diameter equals the max
    eccentricity of the identity on the A side and on the B side.
    """

    def cost(S):
        Si = [inv(g) for g in S]
        total = 0
        for src in (0, N):
            seen = bytearray(2 * N)
            seen[src] = 1
            frontier = [src]
            count = 1
            for _ in range(D):
                nxt = []
                for v in frontier:
                    if v < N:
                        for g in S:
                            w = N + mul(v, g)
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                    else:
                        y = v - N
                        for gi in Si:
                            w = mul(y, gi)
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                if not nxt:
                    break
                count += len(nxt)
                frontier = nxt
            total += 2 * N - count
        return total

    while time.monotonic() < t_end:
        S = rng.sample(range(N), d)
        c = cost(S)
        stale = 0
        while c > 0 and stale < 300:
            if time.monotonic() >= t_end:
                return None
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in S:
                stale += 1
                continue
            S2 = S[:]
            S2[i] = g
            c2 = cost(S2)
            if c2 <= c:
                stale = 0 if c2 < c else stale + 1
                S, c = S2, c2
            else:
                stale += 1
        if c == 0:
            return S
    return None


def _search_order(N, d, D, rng, t_end):
    """Try to find a valid group lift of order N within the time budget."""
    if N < d:
        return None
    cands = _group_candidates(N, rng)
    for idx, (m, k, r) in enumerate(cands):
        now = time.monotonic()
        if now >= t_end:
            break
        per = (t_end - now) / (len(cands) - idx)
        try:
            if k == 1:
                order, mul, inv = lib.cyclic_group(m)
            else:
                order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        S = _hill(order, mul, inv, d, D, rng, now + per)
        if S is None:
            continue
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.75 * time_limit, time_limit - 3.0))

    # Calibration: projective plane incidence meets the Moore bound for D = 3.
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best = _fallback(d, D)
    if d < 1 or D < 1:
        return best

    rng = random.Random(seed)
    lo, hi = 0, None
    N = max(d + 1, min(1000, lib.moore_bound(d, D) // 8))

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.2 or N < d + 1:
            break
        budget_end = now + min(remaining, max(4.0, remaining * 0.2))
        res = _search_order(N, d, D, rng, budget_end)
        if res is not None:
            if res[0] > best[0]:
                best = res
            lo = max(lo, N)
            if hi is not None and N >= hi:
                hi = None
            if hi is None:
                N = lo + max(4, lo // 25)
            else:
                N = (lo + hi) // 2 if hi - lo > 1 else hi
        else:
            hi = N if hi is None else min(hi, N)
            if lo == 0:
                N = N - max(4, N // 20)
            else:
                N = (lo + hi) // 2 if hi - lo > 1 else hi

    return best
