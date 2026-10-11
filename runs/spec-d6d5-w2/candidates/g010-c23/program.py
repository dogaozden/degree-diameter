import math
import random
import time

import numpy as np

import lib

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Algebraic candidates (cheap, used as valid fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: d-regular bipartite graphs on n + n vertices, annealed by
# 2-switches. Diameter is measured with packed uint64 bitsets in numpy.
#
# Representation: edge e joins A-vertex ea[e] to B-vertex eb[e]. Every A and
# every B vertex has exactly d incident edges. A 2-switch on edges e1, e2
# replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1), which keeps all degrees.
#
# Growth: splice d edges into a new A vertex x and a new B vertex y. Old
# degrees are preserved, so the graph stays d-regular and bipartite. Then
# anneal the bad-pair count back to zero.
# ----------------------------------------------------------------------------

def _cost(n, d, D, ea, eb, oa):
    """Ordered count of vertex pairs at distance > D (0 means diameter <= D)."""
    N = 2 * n
    ob = np.argsort(eb, kind="stable")
    nbr = np.empty((N, d), dtype=np.int64)
    nbr[:n] = eb[oa].reshape(n, d) + n
    nbr[n:] = ea[ob].reshape(n, d)
    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    R = np.zeros((N, W), dtype=np.uint64)
    R[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        Rn = R.copy()
        for s in range(d):
            Rn |= R[nbr[:, s]]
        R = Rn
    total = int(_POP8[R.view(np.uint8)].sum())
    return N * N - total


def _anneal(n, d, D, ea, eb, end, rng, T0):
    """Anneal 2-switches on the edge list until the bad-pair count is zero or time runs out.

    Returns (best_cost, ea, best_eb). ea is never modified.
    """
    eb = eb.copy()
    E = n * d
    oa = np.argsort(ea, kind="stable")
    M = np.zeros((n, n), dtype=bool)
    M[ea, eb] = True
    cur = _cost(n, d, D, ea, eb, oa)
    best, best_eb = cur, eb.copy()
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        T = T0 * (1.0 - (now - t0) / span) + 0.3
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1 = int(ea[e1])
        a2 = int(ea[e2])
        b1 = int(eb[e1])
        b2 = int(eb[e2])
        if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
            continue
        eb[e1] = b2
        eb[e2] = b1
        M[a1, b1] = False
        M[a2, b2] = False
        M[a1, b2] = True
        M[a2, b1] = True
        new = _cost(n, d, D, ea, eb, oa)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best = cur
                best_eb = eb.copy()
        else:
            eb[e1] = b1
            eb[e2] = b2
            M[a1, b2] = False
            M[a2, b1] = False
            M[a1, b1] = True
            M[a2, b2] = True
    return best, ea, best_eb


def _splice(n, d, ea, eb, rng):
    """Add one A vertex n and one B vertex n by splicing a d-matching of existing edges.

    Returns (n + 1, ea, eb) or None if no suitable matching was found.
    """
    E = len(ea)
    if E < d:
        return None
    used_a, used_b, chosen = set(), set(), []
    tries = 0
    while len(chosen) < d and tries < 20000:
        tries += 1
        i = rng.randrange(E)
        a = int(ea[i])
        b = int(eb[i])
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
    if len(chosen) < d:
        return None
    mask = np.ones(E, dtype=bool)
    mask[chosen] = False
    ch = np.array(chosen, dtype=np.int64)
    a_arr = ea[ch]
    b_arr = eb[ch]
    x = n
    y = n
    new_ea = np.concatenate([ea[mask], np.full(d, x, dtype=np.int64), a_arr])
    new_eb = np.concatenate([eb[mask], b_arr, np.full(d, y, dtype=np.int64)])
    return n + 1, new_ea, new_eb


def _search(d, D, rng, deadline):
    """Grow a d-regular bipartite graph with diameter <= D. Returns (n, ea, eb) or None."""
    n = d + 1
    S = rng.sample(range(n), d)
    a_idx = np.repeat(np.arange(n, dtype=np.int64), d)
    s_idx = np.tile(np.array(S, dtype=np.int64), n)
    ea = a_idx
    eb = (a_idx + s_idx) % n

    c, ea, eb = _anneal(n, d, D, ea, eb, deadline, rng, 6.0)
    if c != 0:
        return None
    best_state = (n, ea, eb)
    k = max(1, n // 30)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        n2, ea2, eb2 = n, ea, eb
        for _ in range(k):
            r = _splice(n2, d, ea2, eb2, rng)
            if r is None:
                break
            n2, ea2, eb2 = r
        if n2 == n:
            break
        att_end = min(deadline, now + max(1.0, remaining / 5.0))
        c, ea3, eb3 = _anneal(n2, d, D, ea2, eb2, att_end, rng, 6.0)
        if c == 0:
            n, ea, eb = n2, ea3, eb3
            best_state = (n, ea, eb)
            k = min(k * 2, max(1, n // 20))
        elif k > 1:
            k = max(1, k // 2)
    return best_state


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Bipartite max degree 2 with diameter D: the cycle C_{2D} is optimal.
        return lib.haar_graph(D, [0, 1])

    # Safe fallback: K_{d,d}, valid for D >= 2.
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

    try:
        found = _search(d, D, rng, deadline)
    except Exception:
        found = None

    if found is not None:
        n, ea, eb = found
        edges = [(int(a), n + int(b)) for a, b in zip(ea.tolist(), eb.tolist())]
        consider(2 * n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
