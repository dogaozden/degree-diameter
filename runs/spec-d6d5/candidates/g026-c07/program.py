import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Main family: bi-Cayley (Haar-type) graphs over a finite group G of order m.
#
# Vertices A_x = x and B_y = m + y. Each voltage s in a set S (|S| = d, distinct)
# gives edges A_x ~ B_{x*s}. Left translation by G is an automorphism, so the
# diameter is at most D iff the eccentricities of A_e and B_e are at most D.
# That needs only two BFS runs, each over 2m vertices.
#
# This is a different construction from the lift-with-annealing search: it uses
# one base vertex per side, so every group of order m gives a graph on 2m
# vertices. Groups are enumerated exhaustively as cyclic groups and
# semidirect products Z_a x|_r Z_b with a*b = m.
# ----------------------------------------------------------------------------

# Known-good group orders for specific cases (record orders as 2 * m).
_SPECIFIC = {(6, 5): 342}


def _groups(m, rng):
    """All cyclic and semidirect groups Z_a x| Z_b of order m that lib can build, shuffled."""
    out = [lib.cyclic_group(m)]
    for a in range(2, m // 2 + 1):
        if m % a:
            continue
        b = m // a
        if b < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) != 1:
                continue
            if pow(r, b, a) != 1 % a:
                continue
            try:
                out.append(lib.semidirect_group(a, b, r))
            except ValueError:
                continue
    rng.shuffle(out)
    return out


def _unreached(m, D, cS, cI):
    """Number of (source, vertex) pairs at distance > D from A_0 and B_0 (zero means valid).

    cS[i][x] = x * s_i (so A_x ~ B_{cS[i][x]}); cI[i][y] = y * s_i^{-1} (so B_y ~ A_{cI[i][y]}).
    """
    N = 2 * m
    total = 0
    for src in (0, m):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < m:
                    for c in cS:
                        v = m + c[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    y = u - m
                    for c in cI:
                        v = c[y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _search_group(m, d, D, mul_fn, inv_fn, rng, t_end, iters):
    """Simulated annealing over the d-element voltage set S in group G. Returns S with zero cost, or None."""
    cols = {}

    def col(s):
        c = cols.get(s)
        if c is None:
            c = [mul_fn(x, s) for x in range(m)]
            cols[s] = c
        return c

    def cost(S):
        cS = [col(s) for s in S]
        cI = [col(inv_fn(s)) for s in S]
        return _unreached(m, D, cS, cI)

    S = rng.sample(range(m), d)
    cur = cost(S)
    T = 2.0
    it = 0
    while cur > 0 and it < iters and time.monotonic() < t_end:
        it += 1
        i = rng.randrange(d)
        t = rng.randrange(m)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = cost(S2)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
        T = max(0.2, T * 0.995)
    return S if cur == 0 else None


def _try(m, d, D, rng, t_end):
    """Search groups of order m for a valid bi-Cayley graph on 2m vertices. Returns (n, edges) or None."""
    if m < d + 1:
        return None
    groups = _groups(m, rng)
    if not groups:
        return None
    gi = 0
    while time.monotonic() < t_end:
        _, mul_fn, inv_fn = groups[gi % len(groups)]
        gi += 1
        S = _search_group(m, d, D, mul_fn, inv_fn, rng, t_end, 150)
        if S is not None:
            edges = [(x, m + mul_fn(x, s)) for x in range(m) for s in S]
            return 2 * m, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.2, 0.8 * time_limit - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph: diameter 3, optimal when d - 1 is a prime power.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    if D < 3 or best_n >= moore:
        return best

    def attempt(m, frac):
        """Try order m with a fraction of the remaining time. Returns True on success."""
        now = time.monotonic()
        t_end = min(deadline, now + frac * max(0.0, deadline - now))
        g = _try(m, d, D, rng, t_end)
        if g is not None and lib.is_valid(g[0], g[1], d, D):
            consider(g[0], g[1])
            return True
        return False

    if (d, D) in _SPECIFIC:
        m0 = _SPECIFIC[(d, D)]
        if attempt(m0, 0.6):
            # Try slightly larger orders to beat the record.
            for m in range(m0 + 1, m0 + 4):
                if time.monotonic() >= deadline:
                    break
                attempt(m, 0.15)
        else:
            # Fall back to slightly smaller orders.
            for m in range(m0 - 1, max(d, m0 - 40), -1):
                if time.monotonic() >= deadline:
                    break
                if attempt(m, 0.3):
                    break
    else:
        # Generic case: exponential ascent, then bisection between last success and failure.
        mmax = min(moore // 2, 1000)
        lo, hi = d, None
        m = d + 1
        while m <= mmax and time.monotonic() < deadline:
            if attempt(m, 0.25):
                lo = m
                m *= 2
            else:
                hi = m
                break
        if hi is not None:
            while hi - lo > 1 and time.monotonic() < deadline:
                mid = (lo + hi) // 2
                if attempt(mid, 0.25):
                    lo = mid
                else:
                    hi = mid

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
