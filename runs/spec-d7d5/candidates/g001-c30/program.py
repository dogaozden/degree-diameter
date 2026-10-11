import math
import random
import time

import lib


def _bad(N, mul, S, invS, D):
    """Count vertices not within distance D of A-identity (vertex 0) or B-identity (vertex N).

    Vertices 0..N-1 form side A, N..2N-1 form side B. Left multiplication is an
    automorphism of the Haar graph over a group, so these two sources suffice.
    The count is 0 exactly when the graph has diameter <= D.
    """
    total = 0
    for start in (0, N):
        seen = bytearray(2 * N)
        seen[start] = 1
        frontier = [start]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for g in S:
                        w = mul(v, g) + N
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    y = v - N
                    for gi in invS:
                        w = mul(y, gi)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - sum(seen)
    return total


def _hill(N, mul, inv, d, D, rng, t_end):
    """Hill-climb a connection set S of d distinct group elements until the Haar graph has diameter <= D."""
    S = rng.sample(range(N), d)
    invS = [inv(g) for g in S]
    bad = _bad(N, mul, S, invS, D)
    while bad > 0 and time.monotonic() < t_end:
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        T = S[:]
        T[i] = c
        iT = [inv(g) for g in T]
        bt = _bad(N, mul, T, iT, D)
        if bt <= bad:  # accept sideways moves to drift across plateaus
            S, invS, bad = T, iT, bt
    return S if bad == 0 else None


def _groups(N, rng):
    """All semidirect products Z_m x|_r Z_k with m*k = N, m >= 2 (cyclic when r = 1, k = 1), shuffled."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 5.0))
    deadline = start + budget

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    rng = random.Random(seed)

    best = None  # (N, mul, S): Haar graph over a group of order N, valid for diameter D
    N = d + 1
    misses = 0
    while time.monotonic() < deadline and misses < 6:
        groups = _groups(N, rng)[:6]
        found = None
        for m, k, r in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            t_end = min(deadline, now + 0.5)
            S = _hill(order, mul, inv, d, D, rng, t_end)
            if S is not None:
                found = (order, mul, S)
                break
        if found is not None:
            best, misses = found, 0
        else:
            misses += 1
        N += 1

    if best is not None:
        N, mul, S = best
        edges = [(x, N + mul(x, g)) for x in range(N) for g in S]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    return fallback
