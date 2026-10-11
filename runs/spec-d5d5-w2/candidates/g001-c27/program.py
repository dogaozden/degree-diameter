import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------------------
# New idea: bi-Cayley graphs over semidirect products Z_m x|_r Z_k.
#
# The graph has vertices (g, side) and joins (g, 0) to (g*s, 1) for s in S.
# Left multiplication is an automorphism, so the diameter is at most D exactly
# when the two roots (e,0) and (e,1) both have eccentricity <= D. Each candidate
# is therefore scored with two numpy BFS runs, and S is improved by local search.
# The group order is searched from the Moore-bound ceiling downward, with the
# per-level time budget doubling on each pass.
# ---------------------------------------------------------------------------


def _groups_of_order(N):
    """All Z_m x|_r Z_k with m*k = N, as (m, k, P) where P[b] = r^b mod m."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, [0] * k))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, [pow(r, b, m) for b in range(k)]))
    return out


class _Group:
    def __init__(self, m, k, P):
        self.m, self.k, self.P = m, k, P
        self.N = m * k
        x = np.arange(self.N, dtype=np.int64)
        a, b = x // k, x % k
        Pb = np.array(P, dtype=np.int64)[b]
        # T[x, y] = x * y, with (a,b)(c,d) = (a + r^b c, b + d).
        self.T = ((a[:, None] + Pb[:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
        self.inv = np.argmax(self.T == 0, axis=1)

    def mul(self, x, y):
        m, k, P = self.m, self.k, self.P
        a, b = divmod(x, k)
        c, dd = divmod(y, k)
        return ((a + P[b] * c) % m) * k + (b + dd) % k

    def score(self, S, D):
        """Number of (root, vertex) pairs at distance > D from the two roots (0 means valid)."""
        N, T = self.N, self.T
        Sinv = self.inv[S]
        missing = 0
        for side in (0, 1):
            r = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
            r[side][0] = True
            f = [r[0].copy(), r[1].copy()]
            for _ in range(D):
                new0 = np.zeros(N, dtype=bool)
                new1 = np.zeros(N, dtype=bool)
                ids = np.flatnonzero(f[0])
                if ids.size:
                    new1[T[np.ix_(ids, S)].ravel()] = True
                ids = np.flatnonzero(f[1])
                if ids.size:
                    new0[T[np.ix_(ids, Sinv)].ravel()] = True
                new0 &= ~r[0]
                new1 &= ~r[1]
                r[0] |= new0
                r[1] |= new1
                f = [new0, new1]
                if not (new0.any() or new1.any()):
                    break
            missing += 2 * N - int(r[0].sum() + r[1].sum())
        return missing


def _climb(G, d, D, rng, deadline, max_stall):
    """Local search over d-element connection sets; returns S with score 0, or None."""
    N = G.N
    if N < d:
        return None
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cur = G.score(S, D)
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        c = rng.randrange(N)
        if (S == c).any():
            continue
        S2 = S.copy()
        S2[i] = c
        s2 = G.score(S2, D)
        if s2 <= cur:
            if s2 < cur:
                stall = 0
            else:
                stall += 1
            S, cur = S2, s2
        else:
            stall += 1
        if stall > max_stall:  # random restart
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            cur = G.score(S, D)
            stall = 0
    return S


def _bicayley(d, D, seed, deadline):
    """Search group orders from the ceiling downward; return (G, S) for the largest found."""
    rng = random.Random(seed)
    Nmax = lib.moore_bound(d, D) // 2
    levels = {}
    for N in range(d, Nmax + 1):
        gs = _groups_of_order(N)
        if gs:
            levels[N] = gs
    best = None
    best_N = d - 1
    budget = 0.04
    while time.monotonic() < deadline and levels:
        found = False
        for N in sorted(levels, reverse=True):
            if N <= best_N:
                break
            cands = rng.sample(levels[N], min(2, len(levels[N])))
            for (m, k, P) in cands:
                now = time.monotonic()
                if now >= deadline:
                    return best
                G = _Group(m, k, P)
                S = _climb(G, d, D, rng, min(deadline, now + budget), 300)
                if S is not None:
                    best = (G, S)
                    best_N = N
                    found = True
                    break
            if found:
                break
        budget *= 2
    return best


def _fallback(d, D):
    n, e = lib.haar_graph(d, range(d))
    if lib.is_valid(n, e, d, D):
        return n, e
    if lib.is_valid(2, [(0, 1)], d, D):
        return 2, [(0, 1)]
    return 1, []


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.75 * time_limit, max(time_limit - 8.0, 0.4 * time_limit))
    deadline = start + budget

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        n, e = lib.projective_plane_incidence(q)
        if lib.is_valid(n, e, d, D):
            return n, e

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass

    try:
        res = _bicayley(d, D, seed, deadline)
    except Exception:
        res = None
    if res is not None:
        G, S = res
        n = 2 * G.N
        e = lib.group_lift(2, [(0, 1, int(s)) for s in S], G.N, G.mul)[1]
        if lib.is_valid(n, e, d, D):
            return n, e

    return _fallback(d, D)
