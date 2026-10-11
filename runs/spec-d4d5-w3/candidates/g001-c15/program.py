"""Cyclic Haar-graph search with an exact bitmask diameter test.

Haar graph H(m, S): a_i ~ b_{(i+s) mod m} for s in S, |S| = d, 0 in S WLOG.
Graph is vertex-transitive on each side, so diameter <= D reduces to two
coverage conditions from a_0, with rotations of m-bit integers:
  A = union of even-length walk sets from a_0 must be all of Z_m,
  B = union of odd-length walk sets must be all of Z_m.
Each test costs about D*d shifts, far cheaper than a BFS on the full graph.
"""
import itertools
import math
import random
import time

import lib


def _covers(m, pos, neg, D):
    """True if every a-side and every b-side residue lies within walk-distance D of a_0."""
    full = (1 << m) - 1

    def step(x, shifts):
        r = 0
        for s in shifts:
            r |= ((x << s) | (x >> (m - s))) & full
        return r

    A, B, x = 1, 0, 1
    for k in range(D):
        if k % 2 == 0:          # a-side -> b-side: add S
            x = step(x, pos)
            B |= x
        else:                   # b-side -> a-side: subtract S
            x = step(x, neg)
            A |= x
        if A == full and B == full:
            return True
    return A == full and B == full


def _candidates(m, d, budget, rng):
    """Yield connection sets containing 0: exhaustive if few, else random samples."""
    total = math.comb(m - 1, d - 1)
    if total <= budget:
        for c in itertools.combinations(range(1, m), d - 1):
            yield (0,) + c
    else:
        for _ in range(budget):
            yield (0,) + tuple(sorted(rng.sample(range(1, m), d - 1)))


def _search_m(m, d, D, budget, rng, deadline):
    """Return a connection set S of size d that makes H(m, S) have diameter <= D, or None."""
    for S in _candidates(m, d, budget, rng):
        if time.monotonic() >= deadline:
            return None
        pos = list(S)
        neg = [(-s) % m for s in S]
        if _covers(m, pos, neg, D):
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Always-valid fallback: K_{d,d} (diameter 2 <= D for D >= 2).
    best_n, best_edges = lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    mu = lib.moore_bound(d, D) // 2  # Haar graph order is 2m
    found_at = {}

    # Phase 1: cheap sweep over all feasible m to locate the frontier.
    for m in range(d + 1, mu + 1):
        if time.monotonic() >= deadline:
            break
        S = _search_m(m, d, D, 2000, rng, deadline)
        if S is not None:
            found_at[m] = S

    best_m = max(found_at) if found_at else d

    # Phase 2: deeper search just above the frontier.
    while time.monotonic() < deadline and best_m + 1 <= mu:
        for m in range(best_m + 1, min(mu, best_m + 6) + 1):
            if time.monotonic() >= deadline:
                break
            S = _search_m(m, d, D, 60000, rng, deadline)
            if S is not None:
                found_at[m] = S
                best_m = m
                break

    # Pick the largest verified graph.
    for m in sorted(found_at, reverse=True):
        if 2 * m <= best_n:
            break
        n, edges = lib.haar_graph(m, found_at[m])
        if lib.is_valid(n, edges, d, D):
            best_n, best_edges = n, edges
            break

    return best_n, best_edges
