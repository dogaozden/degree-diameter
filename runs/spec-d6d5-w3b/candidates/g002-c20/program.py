import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence and Araujo-Pardo-Lopez (D >= 3).
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
# Main new family: Haar graphs H(Z_m, S) with |S| = d, searched by hill-climb.
#
# H(Z_m, S) has a_i ~ b_j iff j - i in S. Translations act on each side, and
# the map a_i -> b_{-i}, b_j -> a_{-j} swaps the sides while preserving edges.
# Hence the diameter is at most D iff every vertex lies within distance D of
# a_0. That gives an O(m*d) cost per candidate (one BFS), far cheaper than the
# generic all-pairs check, so the search can explore many more connection sets.
# The cost is the number of vertices not reached from a_0 (zero means valid).
# ----------------------------------------------------------------------------

def _unreached(m, S, D):
    """Number of the 2m vertices of H(Z_m, S) at distance > D from a_0."""
    seen_a = bytearray(m)
    seen_b = bytearray(m)
    seen_a[0] = 1
    frontier = [0]
    count = 1
    side = 0
    for _ in range(D):
        nxt = []
        if side == 0:
            for i in frontier:
                for s in S:
                    j = (i + s) % m
                    if not seen_b[j]:
                        seen_b[j] = 1
                        nxt.append(j)
        else:
            for j in frontier:
                for s in S:
                    i = (j - s) % m
                    if not seen_a[i]:
                        seen_a[i] = 1
                        nxt.append(i)
        count += len(nxt)
        frontier = nxt
        side ^= 1
        if not frontier:
            break
    return 2 * m - count


def _haar_search(d, D, m, rng, deadline):
    """Hill-climb a connection set S (|S| = d, 0 in S) so that H(Z_m, S) has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def random_set():
        return [0] + rng.sample(others, d - 1)

    S = random_set()
    c = _unreached(m, S, D)
    stale = 0
    while c > 0 and time.monotonic() < deadline:
        # Replace one nonzero element by a fresh residue.
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        while x in S:
            x = rng.randrange(1, m)
        T = S[:]
        T[i] = x
        ct = _unreached(m, T, D)
        if ct <= c:
            if ct < c:
                stale = 0
            else:
                stale += 1
            S, c = T, ct
        else:
            stale += 1
        if stale > 3000:
            # Random restart to escape a plateau.
            S = random_set()
            c = _unreached(m, S, D)
            stale = 0
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Haar-graph ladder: try increasing m, each with a growing search budget.
    # Success raises m; repeated failure at the same m gets more time.
    if best_n < moore:
        m = max(d + 1, best_n // 2 + 1)
        budget = 2.0
        while time.monotonic() < deadline and 2 * m <= moore:
            dl = min(deadline, time.monotonic() + budget)
            S = _haar_search(d, D, m, rng, dl)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                m = max(m + 1, best_n // 2 + 1)
                budget = 2.0
            else:
                budget = min(budget * 2.0, 30.0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
