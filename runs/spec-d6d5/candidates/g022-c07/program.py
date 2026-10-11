import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured fallbacks: projective plane incidence and the Araujo-Pardo-Lopez
# graph (both diameter 3, so valid for any D >= 3).
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
# Bold new family for D >= 5: unstructured bipartite search.
#
# Start from a Haar graph on Z_h (h vertices per side, d shifts, so d-regular
# and simple). Then run simulated annealing over degree-preserving double-edge
# swaps, minimising the number of ordered vertex pairs at distance > D. A
# zero-cost state is a valid graph with 2h vertices. The size h is adjusted
# between attempts: up after success, down after failure.
# ----------------------------------------------------------------------------

def _bad(N, nbr, D):
    """Ordered pairs at distance > D (bit-parallel). Zero iff diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return N * N - sum(r.bit_count() for r in reach)


def _swap(nbr, E, e1, e2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Calling it again reverts."""
    a1, b1 = E[e1]
    a2, b2 = E[e2]
    nbr[a1][nbr[a1].index(b1)] = b2
    nbr[b1][nbr[b1].index(a1)] = a2
    nbr[a2][nbr[a2].index(b2)] = b1
    nbr[b2][nbr[b2].index(a2)] = a1
    E[e1] = (a1, b2)
    E[e2] = (a2, b1)


def _haar_nbr(h, S):
    nbr = [[h + (i + s) % h for s in S] for i in range(h)]
    nbr += [[(j - s) % h for s in S] for j in range(h)]
    return nbr


def _haar_start(h, d, rng, tries):
    """Best of several random shift sets S (|S| = d) in Z_h, by bad-pair count."""
    best = None
    for _ in range(tries):
        S = rng.sample(range(h), d)
        c = _bad(2 * h, _haar_nbr(h, S), 5)
        if best is None or c < best[0]:
            best = (c, S)
    return best[1]


def _anneal(h, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with h + h vertices. Returns (n, edges) or None."""
    N = 2 * h
    S = _haar_start(h, d, rng, 10)
    nbr = _haar_nbr(h, S)
    E = [(i, h + (i + s) % h) for i in range(h) for s in S]
    cost = _bad(N, nbr, D)
    T = 3.0
    while cost and time.monotonic() < deadline:
        e1 = rng.randrange(len(E))
        e2 = rng.randrange(len(E))
        a1, b1 = E[e1]
        a2, b2 = E[e2]
        # Reject moves that would create a double edge or a self-pair.
        if b2 in nbr[a1] or b1 in nbr[a2]:
            continue
        _swap(nbr, E, e1, e2)
        new = _bad(N, nbr, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _swap(nbr, E, e1, e2)
        T = max(0.5, T * 0.9995)
    if cost == 0:
        return N, [(a, b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit   # leave a margin for final checks
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2), valid for D >= 2.
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

    if D >= 5 and d >= 2:
        rng = random.Random(seed)
        M = lib._moore_bound(d, D)
        h = max(d + 1, int(0.2 * M))   # 0.4 * Moore bound as the first target
        while time.monotonic() < deadline:
            now = time.monotonic()
            rem = deadline - now
            dl = min(deadline, now + max(3.0, 0.35 * rem))
            res = _anneal(h, d, D, rng, dl)
            if res is not None:
                consider(res[0], res[1])
                h = int(h * 1.01) + 1
            else:
                h = max(d + 1, int(h * 0.985))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
