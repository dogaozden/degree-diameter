import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact families (kept as a fallback floor where they apply).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bipartite d-regular graphs built from random perfect matchings,
# then driven to diameter <= D by 2-switch simulated annealing.
#
# Switches (a,b),(c,e) -> (a,e),(c,b) keep every degree at d, keep the graph
# bipartite (left side = 0..s-1, right side = s..2s-1), and keep it simple.
# The cost is the number of ordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, E, D):
    """Ordered count of vertex pairs at distance > D, via bitmask BFS (E = vertex pairs)."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _random_regular(s, d, rng):
    """Union of d random perfect matchings between left and right sides of size s.

    Returns a list of (left, right) index pairs with all pairs distinct, or None.
    """
    used = set()
    E = []
    for _ in range(d):
        ok = False
        for _ in range(2000):
            p = list(range(s))
            rng.shuffle(p)
            if all((a, p[a]) not in used for a in range(s)):
                ok = True
                break
        if not ok:
            return None
        for a in range(s):
            used.add((a, p[a]))
            E.append((a, p[a]))
    return E


def _anneal(s, D, E0, deadline, rng, T0=2.0):
    """Anneal 2-switches on a regular bipartite graph until diameter <= D.

    Returns the list of (left, right) pairs on success, else None.
    """
    n = 2 * s
    E = list(E0)
    eset = set(E)

    def verts(pairs):
        return [(a, s + b) for a, b in pairs]

    cur = _bad_pairs(n, verts(E), D)
    best, best_E = cur, list(E)
    m = len(E)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.05, T0 * (1.0 - (now - start) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        new = _bad_pairs(n, verts(E), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
            if cur < best:
                best, best_E = cur, list(E)
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return best_E if best == 0 else None


def _anneal_search(d, D, moore, deadline, rng, best_n, consider):
    """Climb the side size s: succeed -> grow, fail -> back off and retry."""
    s_try = max(d + 2, best_n // 2)
    step = 8
    while time.monotonic() < deadline - 1.0 and 2 * s_try <= moore:
        remaining = deadline - time.monotonic()
        budget = min(remaining - 0.5, max(4.0, remaining / 3.0))
        if budget <= 0.5:
            break
        att_end = time.monotonic() + budget
        E0 = _random_regular(s_try, d, rng)
        res = None
        if E0 is not None:
            res = _anneal(s_try, D, E0, att_end, rng)
        if res is not None:
            consider(2 * s_try, [(a, s_try + b) for a, b in res])
            s_try += step
        else:
            s_try = max(d + 2, s_try - 3)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

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

    # Main new construction: random regular bipartite + switch annealing.
    if d >= 3 and D >= 3 and best_n < moore:
        _anneal_search(d, D, moore, deadline, rng, best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
