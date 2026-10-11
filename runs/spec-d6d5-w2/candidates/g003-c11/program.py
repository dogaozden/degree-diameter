import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured fallbacks: projective plane incidence (D >= 3) and the
# Araujo-Pardo-Lopez graph (D >= 3, d = q + 2). Both are small and valid.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
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
# New family: unstructured bipartite d-regular graphs found by local search.
#
# State: N left vertices (0..N-1) and N right vertices (N..2N-1), with the
# edge list (ea[i], eb[i]) where ea = left index, eb = right index.
# Every vertex has degree exactly d.
#
# Moves:
#   * degree-preserving double-edge swaps, accepted by Metropolis on the
#     number of ordered vertex pairs at distance > D;
#   * growth by one vertex per side: remove a d-matching (a_k, b_k) and
#     reconnect a_k to a new right vertex and b_k to a new left vertex.
#     The result stays d-regular, so growth is cheap warm-start.
# ----------------------------------------------------------------------------

def _bad_pairs_regular(N, ea, eb, D):
    """Number of ordered vertex pairs at distance > D (zero iff the graph has diameter <= D)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in zip(ea, eb):
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(N, ea, eb, eset, D, deadline, rng, T=0.4):
    """Double-edge-swap annealing until diameter <= D or the deadline. Returns the final cost."""
    cost = _bad_pairs_regular(N, ea, eb, D)
    m = len(ea)
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1, a2, b2 = ea[i], eb[i], ea[j], eb[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in eset or (a2, b1) in eset:
            continue
        eb[i] = b2
        eb[j] = b1
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        new = _bad_pairs_regular(N, ea, eb, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            eb[i] = b1
            eb[j] = b2
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return cost


def _grow(N, ea, eb, eset, d, rng):
    """Add one left and one right vertex (both index N), keeping d-regularity.

    Returns True on success. On failure nothing is modified.
    """
    m = len(ea)
    pick = None
    for _ in range(30):
        order = list(range(m))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            a, b = ea[idx], eb[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            pick = chosen
            break
    if pick is None:
        return False
    pairs = [(ea[idx], eb[idx]) for idx in pick]
    for idx, (a, b) in zip(pick, pairs):
        eset.discard((a, b))
        eset.add((a, N))
        eb[idx] = N
    for a, b in pairs:
        ea.append(N)
        eb.append(b)
        eset.add((N, b))
    return True


def _local_search(d, D, deadline, rng):
    """Grow a d-regular bipartite graph while it keeps diameter <= D. Returns (N, ea, eb) or None."""
    N = d
    ea = [a for a in range(d) for _ in range(d)]
    eb = [b for _ in range(d) for b in range(d)]
    eset = set(zip(ea, eb))
    best = None
    while time.monotonic() < deadline:
        cost = _anneal(N, ea, eb, eset, D, deadline, rng)
        if cost != 0:
            break
        best = (N, list(ea), list(eb))
        grown = False
        for _ in range(20):
            if _grow(N, ea, eb, eset, d, rng):
                grown = True
                break
        if not grown:
            break
        N += 1
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and d >= 2:
        try:
            rng = random.Random(seed * 1000003 + d * 101 + D)
            res = _local_search(d, D, deadline, rng)
            if res is not None:
                N, ea, eb = res
                edges = [(a, N + b) for a, b in zip(ea, eb)]
                consider(2 * N, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
