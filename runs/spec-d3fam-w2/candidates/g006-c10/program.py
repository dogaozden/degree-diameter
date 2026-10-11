import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Cyclic group of order N plus semidirect products Z_m x| Z_k of order N (r = 1 gives direct products)."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _hill_climb(k, N, mul, rng, end, d, patience=300):
    """Search voltages on a random bipartite d-regular base with k+k vertices, lifted over a group of order N.

    The objective is the number of vertex pairs at distance > 3 in the lift. Returns (n, edges)
    with zero bad pairs, or None if the time budget ends first.
    """
    while time.monotonic() < end:
        # Base structure: d layers, each a permutation matching A-vertices to B-vertices.
        skel = []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                skel.append((i, k + p[i]))
        gs = [rng.randrange(N) for _ in skel]

        n, edges = lib.group_lift(2 * k, [(u, v, g) for (u, v), g in zip(skel, gs)], N, mul)
        cost = lib.bad_pairs(n, edges, 3)
        stall = 0
        while cost > 0 and stall < patience and time.monotonic() < end:
            i = rng.randrange(len(gs))
            old = gs[i]
            gs[i] = rng.randrange(N)
            n2, e2 = lib.group_lift(2 * k, [(u, v, g) for (u, v), g in zip(skel, gs)], N, mul)
            c = lib.bad_pairs(n2, e2, 3)
            if c <= cost:
                stall = stall + 1 if c == cost else 0
                cost = c
                n, edges = n2, e2
            else:
                gs[i] = old
                stall += 1
        if cost == 0:
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Different construction: small bipartite base multigraphs (k+k vertices, d-regular)
    # lifted over groups of order N, with voltages found by hill climbing on the
    # true diameter-3 criterion. Candidates are tried in ascending order of order 2kN,
    # so the first success is the smallest improvement and the sweep continues upward.
    moore = lib.moore_bound(d, 3)
    cands = sorted({(2 * k * N, k, N)
                    for k in (1, 2, 3, 4)
                    for N in range(2, moore // (2 * k) + 1)
                    if best_n < 2 * k * N <= moore})

    idx = 0
    while idx < len(cands):
        n_c, k, N = cands[idx]
        idx += 1
        if n_c <= best_n:
            continue
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        left = len(cands) - idx + 1
        share = min(remaining, 2.0 * remaining / left)
        end = now + share
        while time.monotonic() < end:
            groups = _group_list(N, rng)
            mul = groups[rng.randrange(len(groups))][1]
            res = _hill_climb(k, N, mul, rng, end, d)
            if res is not None:
                consider(*res)
                break

    return best
