import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy.
#
# Baseline: K_{d,d}, plus PG(2,q) incidence and the Araujo-Pardo-Lopez graph
# for D = 3. These stay as fallbacks for every case.
#
# Main search (D >= 4): bi-Cayley graphs over a group G of order N.
#   A-vertices a_g (0..N-1) and B-vertices b_h (N..2N-1).
#   Edge a_g ~ b_{g*s} for each s in a connection set S with |S| = d.
#   Left multiplication is an automorphism that is transitive on each side,
#   so the diameter is <= D iff every vertex is within D of a_e and of b_e.
#   Both checks run as vectorised numpy BFS, which is far cheaper than a
#   full all-pairs check.
#
# Groups are semidirect products Z_a x| Z_b (a*b = N), so non-cyclic groups
# are tried as well. For each target order N, simulated-annealing hill-climbs
# over S. The target order grows on success and backs off on failure.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


class _Group:
    """Finite group given by mul/inv on codes 0..order-1, with cached right-multiplication permutations."""

    def __init__(self, order, mul, inv):
        self.order = order
        self.mul = mul
        self.inv = inv
        self._cache = {}

    def perm(self, s):
        """numpy array p with p[g] = g * s."""
        p = self._cache.get(s)
        if p is None:
            p = np.array([self.mul(g, s) for g in range(self.order)], dtype=np.int64)
            self._cache[s] = p
        return p


def _sample_group(N, rng):
    """Random semidirect product Z_a x| Z_b of order N, or None if none was found."""
    bs = [b for b in range(1, min(12, N) + 1) if N % b == 0 and N // b >= 2]
    if not bs:
        return None
    for _ in range(20):
        b = rng.choice(bs)
        a = N // b
        if b == 1:
            r = 1
        else:
            cands = [r for r in range(1, a)
                     if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, inv = lib.semidirect_group(a, b, r)
        return _Group(order, mul, inv)
    return None


def _cost(N, D, S, grp):
    """Number of vertices not within distance D of a_e or of b_e. Zero means valid."""
    Pm = np.stack([grp.perm(s) for s in S])                       # a_g -> b_{g s}
    Qm = np.stack([grp.perm(grp.inv(s)) for s in S])              # b_h -> a_{h s^-1}
    total = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            parts = []
            a = frontier[frontier < N]
            if a.size:
                parts.append((N + Pm[:, a]).ravel())
            b = frontier[frontier >= N] - N
            if b.size:
                parts.append(Qm[:, b].ravel())
            if not parts:
                break
            mark = np.zeros(2 * N, dtype=bool)
            mark[np.concatenate(parts)] = True
            mark &= ~seen
            seen |= mark
            frontier = np.flatnonzero(mark)
            if frontier.size == 0:
                break
        total += 2 * N - int(seen.sum())
    return total


def _climb(N, D, d, grp, rng, deadline):
    """Hill-climb a connection set S (|S| = d, distinct) until cost 0 or the deadline."""
    S = rng.sample(range(N), d)
    cur = _cost(N, D, S, grp)
    T = 1.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = _cost(N, D, S, grp)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
        T = max(0.2, T * 0.9995)
    return (list(S) if cur == 0 else None), cur


def _edges(N, S, grp):
    """Full bi-Cayley graph: 2N vertices, A = 0..N-1, B = N..2N-1."""
    perms = [grp.perm(s) for s in S]
    E = []
    for g in range(N):
        for p in perms:
            E.append((g, N + int(p[g])))
    return 2 * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D == 2 or D == 3 or d < 2:
        return best

    # Main search: bi-Cayley graphs over semidirect products, growing the side order N.
    side = max(best_n // 2, d)
    step = max(1, side // 60)
    attempt_time = 4.0
    while time.monotonic() < deadline:
        N = side + step
        grp = _sample_group(N, rng)
        if grp is None:
            step = max(1, step // 2)
            continue
        limit = min(deadline, time.monotonic() + attempt_time)
        S, _ = _climb(N, D, d, grp, rng, limit)
        ok = False
        if S is not None:
            n, e = _edges(N, S, grp)
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                ok = True
        if ok:
            side = best_n // 2
            step = max(1, side // 60)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
