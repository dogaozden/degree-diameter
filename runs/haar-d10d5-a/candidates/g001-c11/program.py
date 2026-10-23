"""Haar-graph search over metacyclic groups Z_m x| Z_k for diameter 5.

New in this version:
  * MetaGroup: precomputed multiplication and inverse tables for Z_m x| Z_k,
    so a connection-set cost is a handful of numpy gathers.
  * Uncovered-seeded moves: the annealer reads the group elements that are still
    missing from (S^-1 S)^2 or (S S^-1)^2 and proposes replacements that put one
    of them directly into S^-1 S (or S S^-1). This covers a missing element at once.
  * Order ladder: groups are tried at increasing orders (fractions of the word
    bound), and each success becomes the fallback for the next level.
"""
import math
import random
import time

import numpy as np

import lib


class MetaGroup:
    """Metacyclic group Z_m x| Z_k with r^k = 1 mod m; element (a, b) is coded a*k + b."""

    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        N = m * k
        self.N = N
        P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int32)
        x = np.arange(N, dtype=np.int32)
        a = x // k
        b = x % k
        # (a, b)(c, d) = (a + r^b c, b + d)
        T = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
        self.mul = T.astype(np.int32)
        nb = (-b) % k
        ia = (-(P[nb] * a)) % m
        self.inv = (ia * k + nb).astype(np.int32)

    def evaluate(self, S):
        """Return (cost, uncovered_A, uncovered_B) for connection set S (int32 array of distinct elements).

        cost = |G \\ (S^-1 S)^2| + |G \\ (S S^-1)^2|; the Haar graph has diameter <= 5 iff cost == 0.
        """
        mul, inv, N = self.mul, self.inv, self.N
        Si = inv[S]
        pa = mul[Si[:, None], S[None, :]].ravel()
        pb = mul[S[:, None], Si[None, :]].ravel()
        A = np.zeros(N, dtype=bool)
        A[pa] = True
        Bm = np.zeros(N, dtype=bool)
        Bm[pb] = True
        Ae = np.flatnonzero(A)
        Be = np.flatnonzero(Bm)
        AA = np.zeros(N, dtype=bool)
        AA[mul[Ae[:, None], Ae[None, :]].ravel()] = True
        BB = np.zeros(N, dtype=bool)
        BB[mul[Be[:, None], Be[None, :]].ravel()] = True
        uA = np.flatnonzero(~AA)
        uB = np.flatnonzero(~BB)
        return len(uA) + len(uB), uA, uB

    def graph(self, S):
        """Haar graph: A-vertex g joins B-vertex N + s*g for each s in S."""
        N = self.N
        g = np.arange(N, dtype=np.int64)
        edges = []
        for s in S:
            hs = self.mul[int(s), :].astype(np.int64) + N
            edges.extend(zip(g.tolist(), hs.tolist()))
        return 2 * N, edges


def _metacyclic(N):
    """All (m, k, r) with m*k = N, r != 1 (non-abelian), gcd(r, m) = 1, r^k = 1 mod m."""
    out = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _anneal(G, d, rng, deadline, K=4, run_len=3000):
    """Anneal a d-element connection set; returns a zero-cost S or None at the deadline."""
    N = G.N
    while time.monotonic() < deadline:
        S = np.array(rng.sample(range(N), d), dtype=np.int32)
        cost, uA, uB = G.evaluate(S)
        for it in range(run_len):
            if cost == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            T = 1.5 * (0.05 ** (it / run_len))
            best_c = None
            for _ in range(K):
                i = rng.randrange(d)
                j = rng.randrange(d - 1)
                if j >= i:
                    j += 1
                if (len(uA) or len(uB)) and rng.random() < 0.7:
                    # Uncovered-seeded move: x = S_j g makes S_j^-1 x = g (A side),
                    # and x = h S_j makes x S_j^-1 = h (B side).
                    if len(uA) and (len(uB) == 0 or rng.random() < 0.5):
                        g = int(uA[rng.randrange(len(uA))])
                        x = int(G.mul[S[j], g])
                    else:
                        h = int(uB[rng.randrange(len(uB))])
                        x = int(G.mul[h, S[j]])
                else:
                    x = rng.randrange(N)
                if np.any(S == x):
                    continue
                S2 = S.copy()
                S2[i] = x
                c2, a2, b2 = G.evaluate(S2)
                if best_c is None or c2 < best_c[0]:
                    best_c = (c2, S2, a2, b2)
            if best_c is None:
                continue
            c2, S2, a2, b2 = best_c
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                S, cost, uA, uB = S2, c2, a2, b2
    return None


def _cyclic_search(d, D, seed, deadline):
    """Fallback: cyclic Haar graphs with a random connection set containing 0."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


# Fractions of the word bound 1 + d(d-1) + d(d-1)^3 used as group-order ladder levels.
TARGET_FRACS = (0.08, 0.12, 0.17, 0.21, 0.24, 0.26, 0.27, 0.28, 0.29, 0.30)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D != 5 or d < 3:
        return _cyclic_search(d, D, seed, deadline)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    ub = 1 + d * (d - 1) + d * (d - 1) ** 3
    best_order = d

    for frac in TARGET_FRACS:
        if time.monotonic() >= deadline:
            break
        t = max(d, int(frac * ub))
        N = t
        cands = None
        while N < t + 200:
            cands = _metacyclic(N)
            if cands:
                break
            N += 1
        if not cands or N <= best_order:
            continue

        now = time.monotonic()
        level_deadline = min(deadline, now + max(4.0, 0.3 * (deadline - now)))
        rng.shuffle(cands)
        preferred = [c for c in cands if c[0] >= 5 and c[1] >= 4]
        cands = preferred or cands
        tries = cands[:4]

        success = None
        for idx, (m, k, r) in enumerate(tries):
            now = time.monotonic()
            if now >= level_deadline:
                break
            cdl = min(level_deadline, now + (level_deadline - now) / (len(tries) - idx))
            G = MetaGroup(m, k, r)
            S = _anneal(G, d, rng, cdl)
            if S is None:
                continue
            n, edges = G.graph(S)
            if lib.is_valid(n, edges, d, D):
                success = (n, edges)
                best_order = G.N
                break

        if success is None:
            break
        best = success

    return best
