import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d} (diameter 2) and the projective-plane incidence graph.
# ----------------------------------------------------------------------------

def _kdd(d):
    """Complete bipartite K_{d,d}: valid for every D >= 2 when d >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: unstructured d-regular bipartite graphs found by simulated
# annealing with degree-preserving 2-switches. The cost is the number of
# vertex pairs at distance greater than D, computed with big-int bitsets.
# This replaces the earlier non-abelian voltage-lift search.
# ----------------------------------------------------------------------------

def _random_bip(M, d, rng, tries=5000):
    """Union of d random perfect matchings between parts of size M (no repeated edges)."""
    S = set()
    E = []
    for _ in range(d):
        ok = False
        for _t in range(tries):
            p = list(range(M))
            rng.shuffle(p)
            if all((a, M + p[a]) not in S for a in range(M)):
                ok = True
                break
        if not ok:
            return None
        for a in range(M):
            e = (a, M + p[a])
            S.add(e)
            E.append(e)
    return E, S


def _bad_pairs(n, E, D):
    """Number of unordered vertex pairs at distance greater than D (unreachable counts too)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(M, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on parts of size M. Returns an edge list or None."""
    n = 2 * M
    st = _random_bip(M, d, rng)
    if st is None:
        return None
    E, S = st
    cost = _bad_pairs(n, E, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T0, T1 = 4.0, 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = T0 * (1.0 - frac) + T1 * frac

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in S or (c, b) in S:
            continue
        # Apply the switch: (a,b),(c,e) -> (a,e),(c,b).
        E[i] = (a, e)
        E[j] = (c, b)
        S.discard((a, b))
        S.discard((c, e))
        S.add((a, e))
        S.add((c, b))
        c2 = _bad_pairs(n, E, D)
        limit = cost - T * math.log(1.0 - rng.random())  # Metropolis threshold
        if c2 <= limit:
            cost = c2
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            S.discard((a, e))
            S.discard((c, b))
            S.add((a, b))
            S.add((c, e))
    return E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, min(0.8 * time_limit, time_limit - 2.0))
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    best = _kdd(d)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    ub = lib.moore_bound(d, D)
    if best[0] >= ub:
        return best

    # Search: grow the part size M while annealing succeeds. Step size adapts.
    step = 8
    while time.monotonic() < end - 0.5:
        now = time.monotonic()
        M = best[0] // 2 + step
        if 2 * M > ub:
            M = ub // 2
        if M <= best[0] // 2:
            break
        budget = max(0.5, (end - now) / 3.0)
        E = _anneal(M, d, D, rng, min(end, now + budget))
        if E is not None:
            consider(2 * M, E)
            step = min(step * 2, 32)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
