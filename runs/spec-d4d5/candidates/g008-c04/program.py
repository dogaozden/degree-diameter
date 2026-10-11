import math
import random
import time

import numpy as np

import lib

TIME_FRAC = 0.8        # fraction of time_limit used overall
TIME_MARGIN = 1.0      # seconds reserved for final validation and return
SLICE_MIN = 0.5        # minimum seconds per growth attempt
SLICE_FRAC = 0.12      # share of remaining time per growth attempt
MAX_FAILS = 4          # consecutive failed growth attempts before stopping


def _reach_bad(A, D):
    """Number of ordered pairs (u, v) with dist(u, v) > D; zero iff diameter <= D and connected."""
    n = A.shape[0]
    Af = A.astype(np.float32)
    R = np.eye(n, dtype=np.float32)
    for _ in range(D):
        Rn = np.minimum(R + R @ Af, 1.0)
        if np.array_equal(Rn, R):
            break
        R = Rn
    return n * n - int(np.count_nonzero(R))


def _set_edge(A, a, b, val):
    A[a, b] = val
    A[b, a] = val


def _anneal(A, E, D, rng, deadline):
    """Double-edge swaps on a bipartite graph (E lists (L, R) pairs, L even, R odd).

    A swap (a,b),(c,d) -> (a,d),(c,b) keeps every degree and the bipartition.
    Modifies A and E in place. Returns the final number of bad ordered pairs.
    """
    cur = _reach_bad(A, D)
    if cur == 0:
        return 0
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        temp = 1.5 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, dd = E[j]
        if a == c or b == dd:
            continue
        if A[a, dd] or A[c, b]:
            continue
        _set_edge(A, a, b, False)
        _set_edge(A, c, dd, False)
        _set_edge(A, a, dd, True)
        _set_edge(A, c, b, True)
        new = _reach_bad(A, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            E[i] = (a, dd)
            E[j] = (c, b)
        else:
            _set_edge(A, a, dd, False)
            _set_edge(A, c, b, False)
            _set_edge(A, a, b, True)
            _set_edge(A, c, dd, True)
    return cur


def _matching(E, d, rng):
    """Indices of d edges with pairwise distinct endpoints (a matching of size d), or None."""
    for _ in range(50):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        usedL, usedR, picks = set(), set(), []
        for k in idx:
            a, b = E[k]
            if a in usedL or b in usedR:
                continue
            usedL.add(a)
            usedR.add(b)
            picks.append(k)
            if len(picks) == d:
                return picks
    return None


def _grow(A, E, d, rng):
    """Add one L vertex x and one R vertex y, both of degree d, by splicing d matching edges.

    Each chosen edge (a, b) becomes (x, b) and (a, y); all old degrees are preserved.
    Returns new (A, E) or None. Inputs are not modified.
    """
    picks = _matching(E, d, rng)
    if picks is None:
        return None
    n = A.shape[0]
    x, y = n, n + 1
    B = np.zeros((n + 2, n + 2), dtype=bool)
    B[:n, :n] = A
    chosen = set(picks)
    F = [e for k, e in enumerate(E) if k not in chosen]
    for k in picks:
        a, b = E[k]
        _set_edge(B, a, b, False)
        _set_edge(B, x, b, True)
        _set_edge(B, a, y, True)
        F.append((x, b))
        F.append((a, y))
    return B, F


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    fallback = lib.haar_graph(d, range(d))

    # Algebraic shortcut: PG(2,q) incidence is Moore-extremal for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    deadline = start + max(0.5, TIME_FRAC * time_limit - TIME_MARGIN)
    rng = random.Random(seed * 7919 + 13 * d + D)

    # Start from K_{d,d} with L = even labels, R = odd labels.
    A = np.zeros((2 * d, 2 * d), dtype=bool)
    E = []
    for i in range(d):
        for j in range(d):
            a, b = 2 * i, 2 * j + 1
            _set_edge(A, a, b, True)
            E.append((a, b))
    best_n, best_e = 2 * d, list(E)

    fails = 0
    while time.monotonic() < deadline - 0.2 and fails < MAX_FAILS:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(SLICE_MIN, SLICE_FRAC * remaining))
        g = _grow(A, E, d, rng)
        if g is None:
            break
        B, F = g
        cost = _anneal(B, F, D, rng, slice_end)
        if cost == 0:
            A, E = B, F
            best_n, best_e = A.shape[0], list(E)
            fails = 0
        else:
            fails += 1

    n = best_n
    edges = [(int(min(u, v)), int(max(u, v))) for u, v in best_e]
    try:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return fallback
