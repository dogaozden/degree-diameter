import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x| Z_k.
#
# Vertices: A_x (x in G) = x, B_y (y in G) = N + y, with |G| = N.
# Connection set S (|S| = d, distinct group elements):
#     A_x ~ B_{x*s} for every s in S.
# Left multiplication by g acts transitively on A and on B separately, and
# preserves edges, so the graph has diameter <= D iff the eccentricities of
# the two identity vertices A_e and B_e are <= D. Bipartite by construction,
# degree exactly d.
#
# Group law on (a, b) coded as a*k + b:  (a,b)*(c,d) = (a + r^b * c, b + d),
# valid when gcd(r, m) = 1 and r^k = 1 mod m (r = 1 gives an abelian group).
# ---------------------------------------------------------------------------


def _groups_of_order(N, rng, cap=6):
    """Candidate (m, k, r) with m*k = N giving valid semidirect products."""
    groups = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            groups.append((1, k, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > cap:
            rs = rng.sample(rs, cap)
        for r in rs:
            groups.append((m, k, r))
    return groups


class _Group:
    def __init__(self, m, k, r, N):
        self.m, self.k, self.N = m, k, N
        X = np.arange(N, dtype=np.int64)
        self.X = X
        self.A = X // k
        self.B = X % k
        self.pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        self.cache = {}

    def perm(self, s):
        """Return (P, Q): P[x] = x*s, Q = inverse of P (Q[y] = y*s^{-1})."""
        hit = self.cache.get(s)
        if hit is None:
            c, dd = divmod(s, self.k)
            P = ((self.A + self.pw[self.B] * c) % self.m) * self.k \
                + (self.B + dd) % self.k
            Q = np.empty(self.N, dtype=np.int64)
            Q[P] = self.X
            hit = (P, Q)
            self.cache[s] = hit
        return hit


def _score(grp, S, D):
    """Number of (source, vertex) pairs NOT within distance D; 0 means valid."""
    N = grp.N
    Ps, Qs = [], []
    for s in S:
        P, Q = grp.perm(s)
        Ps.append(P)
        Qs.append(Q)
    total = 0
    for src in (0, N):
        vis = np.zeros(2 * N, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            parts = []
            fa = frontier[frontier < N]
            fb = frontier[frontier >= N] - N
            if fa.size:
                for P in Ps:
                    parts.append(P[fa] + N)
            if fb.size:
                for Q in Qs:
                    parts.append(Q[fb])
            if not parts:
                break
            cand = np.concatenate(parts)
            new = np.unique(cand[~vis[cand]])
            if new.size == 0:
                break
            vis[new] = True
            frontier = new
        total += 2 * N - int(vis.sum())
    return total


def _search(grp, d, D, rng, deadline, steps=400):
    """Hill climb over connection sets S; return a valid S or None."""
    N = grp.N
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = _score(grp, S, D)
        for _ in range(steps):
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            t = rng.randrange(N)
            if t in S:
                continue
            S2 = S[:]
            S2[i] = t
            sc = _score(grp, S2, D)
            if sc <= cur or rng.random() < 0.03:
                S, cur = S2, sc
        if cur == 0:
            return S
    return None


def _edges_from(grp, S):
    N = grp.N
    edges = []
    X = range(N)
    for s in S:
        P, _ = grp.perm(s)
        Pl = P.tolist()
        edges.extend((x, N + Pl[x]) for x in X)
    return 2 * N, edges


def _search_build(d, D, seed, time_limit, start, fallback):
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    deadline = start + max(0.5, min(0.75 * time_limit, time_limit - 3))
    best = [fallback]
    rng = random.Random(seed)
    moore_half = lib.moore_bound(d, D) // 2

    def try_N(N, budget):
        now = time.monotonic()
        end = min(deadline, now + budget)
        if end <= now or N > moore_half or N <= d:
            return False
        groups = _groups_of_order(N, rng)
        if not groups:
            return False
        rng.shuffle(groups)
        groups = groups[:6]
        slice_ = (end - now) / len(groups)
        for m, k, r in groups:
            grp = _Group(m, k, r, N)
            S = _search(grp, d, D, rng,
                        min(end, time.monotonic() + slice_))
            if S is not None:
                n, edges = _edges_from(grp, S)
                if n > best[0][0] and lib.is_valid(n, edges, d, D):
                    best[0] = (n, edges)
                    return True
        return False

    # Gallop upward from the known K_{d,d} half-order.
    lo, hi = d, None
    while time.monotonic() < deadline:
        N = max(lo + 1, int(lo * 1.25))
        if N > moore_half:
            break
        if try_N(N, 2.0):
            lo = N
        else:
            hi = N
            break
    # Bisect between the last success and the first failure.
    if hi is not None:
        while hi - lo > 1 and time.monotonic() < deadline:
            mid = (lo + hi) // 2
            if try_N(mid, 3.0):
                lo = mid
            else:
                hi = mid
    # Spend remaining time trying to push past the current best.
    while time.monotonic() < deadline:
        if lo + 1 > moore_half:
            break
        if try_N(lo + 1, 4.0):
            lo += 1
    return best[0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    fallback = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    try:
        n, edges = _search_build(d, D, seed, time_limit, start, fallback)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return fallback
