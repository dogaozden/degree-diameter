import math
import random
import time

import numpy as np

import lib


def _groups(N):
    """Candidate groups of order N as (m, k, r): Z_m semidirect Z_k with action r (k = 1 gives Z_N)."""
    out = [(N, 1, 1)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table of Z_m x| Z_k with element (a, b) coded as a*k + b."""
    N = m * k
    xs = np.arange(N, dtype=np.int64)
    a = xs // k
    b = xs % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    Bn = (b[:, None] + b[None, :]) % k
    T = A * k + Bn
    inv = np.argmax(T == 0, axis=1)
    return N, T.tolist(), inv.tolist()


def _cost(S, Sinv, T, N, D):
    """Number of vertices not within distance D of a_1 or b_1 (zero iff the bi-Cayley graph has diameter <= D)."""
    tot = 0
    for side in (0, 1):
        seenA = bytearray(N)
        seenB = bytearray(N)
        if side == 0:
            seenA[0] = 1
            fa, fb = [0], []
        else:
            seenB[0] = 1
            fa, fb = [], [0]
        cnt = 1
        for _ in range(D):
            if not fa and not fb:
                break
            nb = []
            for x in fa:
                row = T[x]
                for g in S:
                    y = row[g]
                    if not seenB[y]:
                        seenB[y] = 1
                        nb.append(y)
            na = []
            for y in fb:
                row = T[y]
                for h in Sinv:
                    x = row[h]
                    if not seenA[x]:
                        seenA[x] = 1
                        na.append(x)
            cnt += len(na) + len(nb)
            fa, fb = na, nb
        tot += 2 * N - cnt
    return tot


def _search(T, inv, N, d, D, rng, deadline):
    """Hill-climb a connection set S of size d in the group so that the bi-Cayley graph has diameter <= D."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        Sinv = [inv[g] for g in S]
        c = _cost(S, Sinv, T, N, D)
        stale = 0
        while c > 0 and stale < 400 and time.monotonic() < deadline:
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in S:
                stale += 1
                continue
            S2 = S[:]
            S2[i] = g
            Sinv2 = Sinv[:]
            Sinv2[i] = inv[g]
            c2 = _cost(S2, Sinv2, T, N, D)
            if c2 <= c:
                stale = 0 if c2 < c else stale + 1
                S, Sinv, c = S2, Sinv2, c2
            else:
                stale += 1
        if c == 0:
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + total

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 1, []

    rng = random.Random(seed)
    hi = min(lib.moore_bound(d, D) // 2, 400)
    PER_N = 0.25

    N = max(d, 1)
    while N <= hi and time.monotonic() < deadline:
        if 2 * N <= best_n or N < d:
            N += 1
            continue
        groups = _groups(N)
        rng.shuffle(groups)
        now = time.monotonic()
        end_N = min(deadline, now + PER_N)
        found = None
        for (m, k, r) in groups:
            now = time.monotonic()
            if now >= end_N:
                break
            Nn, T, inv = _table(m, k, r)
            slice_end = min(end_N, now + max(0.03, PER_N / len(groups)))
            S = _search(T, inv, Nn, d, D, rng, slice_end)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = []
            for x in range(N):
                row = T[x]
                for g in S:
                    edges.append((x, N + row[g]))
            n2 = 2 * N
            if n2 > best_n and lib.is_valid(n2, edges, d, D):
                best_n, best_e = n2, edges
        N += 1

    return best_n, best_e
