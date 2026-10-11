import math
import random
import time

import lib


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} (diameter 2), or a single edge, or a lone vertex."""
    if D >= 2 and d >= 1:
        n, edges = lib.haar_graph(d, range(d))
    elif D >= 1 and d >= 1:
        n, edges = 2, [(0, 1)]
    else:
        n, edges = 1, []
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 1, []


def _groups(N):
    """All semidirect products Z_m x| Z_k with m*k = N, as (m, k, r) triples."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(1, max(m, 2)):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _search_group(N, T, ginv, d, D, rng, deadline):
    """Simulated-style local search for a connection set S (|S| = d) giving a bi-Cayley graph of diameter <= D.

    The lift of the 2-vertex base with darts S is left-transitive on each side, so its diameter
    is certified by two BFS runs: one from left identity and one from right identity.
    Returns S (list of group elements) or None.
    """
    two = 2 * N

    def unreached(src, S, Sinv):
        seen = bytearray(two)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = T[v]
                    for g in S:
                        w = N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = T[v - N]
                    for gi in Sinv:
                        w = row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        return two - cnt

    def cost(S):
        Sinv = [ginv[g] for g in S]
        return unreached(0, S, Sinv) + unreached(N, S, Sinv)

    if d > N:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        c = cost(S)
        stall = 0
        while c > 0 and stall < 4000 and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                stall += 1
                continue
            S2 = S[:]
            S2[i] = x
            c2 = cost(S2)
            if c2 <= c:
                stall = 0 if c2 < c else stall + 1
                S, c = S2, c2
            else:
                stall += 1
        if c == 0:
            return S
    return None


def _try_order(N, d, D, rng, deadline):
    """Try to find a valid bi-Cayley lift with left/right parts of order N. Returns (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups:
        now = time.monotonic()
        if now >= deadline:
            break
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        slice_end = min(deadline, time.monotonic() + 2.0)
        S = _search_group(N, T, ginv, d, D, rng, slice_end)
        if S is not None:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.6 * time_limit, time_limit - 8.0))
    deadline = start + total

    # Proven-optimal projective plane incidence graphs for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    best = _fallback(d, D)
    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    max_N = lib.moore_bound(d, D) // 2
    lo = max(1, best[0] // 2)   # largest order known feasible
    hi = max_N + 1              # assumed infeasible

    # Bisection over the group order N (graph has 2N vertices).
    while lo + 1 < hi:
        now = time.monotonic()
        if now >= deadline:
            break
        mid = (lo + hi) // 2
        remaining = deadline - now
        trial_deadline = now + max(1.0, remaining / 3.0)
        result = _try_order(mid, d, D, rng, min(trial_deadline, deadline))
        if result is not None:
            n, edges = result
            if lib.is_valid(n, edges, d, D) and n > best[0]:
                best = (n, edges)
            lo = mid
        else:
            hi = mid

    return best
