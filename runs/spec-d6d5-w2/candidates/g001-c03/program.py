import math
import random
import time

import numpy as np

import lib


class _Group:
    """Semidirect product Z_m x|_r Z_k, element (a, b) coded as a*k + b.

    Bi-Cayley graph: A_x ~ B_{x*s} for s in S. Left multiplication is an automorphism,
    so all distances are covered by BFS from A_e and from B_e.
    """

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        self.powers = [pow(r, b, m) for b in range(k)]
        self.pw = np.array(self.powers, dtype=np.int64)
        X = np.arange(self.N, dtype=np.int64)
        self.a = X // k
        self.b = X % k
        self._cache = {}

    def _perm_right(self, s):
        c, d = divmod(s, self.k)
        na = (self.a + self.pw[self.b] * c) % self.m
        nb = (self.b + d) % self.k
        return na * self.k + nb

    def _inv(self, s):
        c, d = divmod(s, self.k)
        x = (-self.powers[(self.k - d) % self.k] * c) % self.m
        y = (-d) % self.k
        return x * self.k + y

    def P(self, s):
        """Array x -> x*s (A side to B side)."""
        if s not in self._cache:
            self._cache[s] = self._perm_right(s)
        return self._cache[s]

    def Q(self, s):
        """Array y -> y*s^{-1} (B side to A side)."""
        return self.P(self._inv(s))

    def bad(self, S, D):
        """Number of (ordered source, target) pairs not within distance D; 0 means valid."""
        N = self.N
        total = 0
        for start in (0, 1):
            visA = np.zeros(N, dtype=bool)
            visB = np.zeros(N, dtype=bool)
            if start == 0:
                visA[0] = True
                side = 0
            else:
                visB[0] = True
                side = 1
            fr = np.array([0], dtype=np.int64)
            for _ in range(D):
                tmp = np.zeros(N, dtype=bool)
                if side == 0:
                    for s in S:
                        tmp[self.P(s)[fr]] = True
                    tmp &= ~visB
                    visB |= tmp
                else:
                    for s in S:
                        tmp[self.Q(s)[fr]] = True
                    tmp &= ~visA
                    visA |= tmp
                fr = np.flatnonzero(tmp)
                side ^= 1
                if fr.size == 0:
                    break
            total += 2 * N - int(visA.sum()) - int(visB.sum())
        return total


def _groups_of_order(N):
    """All semidirect products Z_m x| Z_k with m*k = N (cyclic case included)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _climb(grp, S, end, rng, D, d):
    """Hill-climb on the connection set S to drive the coverage defect to zero."""
    N = grp.N
    cur = grp.bad(S, D)
    stagn = 0
    while cur > 0 and time.monotonic() < end:
        i = rng.randrange(d)
        g = rng.randrange(N)
        stagn += 1
        if g not in S:
            S2 = S[:]
            S2[i] = g
            sc = grp.bad(S2, D)
            if sc <= cur:
                if sc < cur:
                    stagn = 0
                S, cur = S2, sc
        if stagn > 400:
            S = rng.sample(range(N), d)
            cur = grp.bad(S, D)
            stagn = 0
    return S, cur


def _try_order(N, d, D, rng, deadline):
    """Try to find a bi-Cayley graph of order 2N with degree d and diameter D."""
    groups = _groups_of_order(N)
    if not groups:
        return None
    rng.shuffle(groups)
    for g in groups[:4]:
        if time.monotonic() >= deadline:
            break
        grp = _Group(*g)
        end = min(deadline, time.monotonic() + 1.0)
        S = rng.sample(range(N), d)
        S, cur = _climb(grp, S, end, rng, D, d)
        if cur == 0:
            edges = []
            for s in S:
                for x, t in enumerate(grp.P(s).tolist()):
                    edges.append((x, N + t))
            n = 2 * N
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))

    if d <= 0 or D <= 0:
        return 1, []

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # Baseline: K_{d,d}, valid when D >= 2.
    best = None
    n0, e0 = lib.haar_graph(d, range(d))
    if lib.is_valid(n0, e0, d, D):
        best = (n0, e0)
    if best is None:
        return 2, [(0, 1)] if D >= 1 else (1, [])

    if D < 2:
        return best

    rng = random.Random(seed)
    Nmax = lib.moore_bound(d, D) // 2
    lo = d
    step = max(1, lo // 8)

    try:
        while time.monotonic() < deadline and lo < Nmax:
            N = lo + step
            if N > Nmax:
                step = max(1, (Nmax - lo) // 2)
                continue
            res = _try_order(N, d, D, rng, deadline)
            if res is not None:
                lo = N
                best = res
                step *= 2
            else:
                if step > 1:
                    step //= 2
    except Exception:
        pass

    return best

