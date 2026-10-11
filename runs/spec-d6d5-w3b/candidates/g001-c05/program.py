import math
import random
import time

import lib


def _specs(N):
    """Groups of order N: the cyclic group Z_N and Z_m x|_r Z_k with m*k = N, k >= 2, r != 1."""
    specs = [("c", N)]
    for m in range(3, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                specs.append(("s", m, k, r))
    return specs


def _make(spec):
    if spec[0] == "c":
        return lib.cyclic_group(spec[1])
    return lib.semidirect_group(spec[1], spec[2], spec[3])


def _table(order, mul, inv):
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    I = [inv(g) for g in range(order)]
    return T, I


def _cost(S, T, I, N, D):
    """Number of (vertex, target) pairs not reached within D from A_e and from B_e.

    The lift of the 2-vertex base graph with connection set S is invariant under left
    multiplication on each side, so diameter <= D holds iff both balls of radius D
    around A_e and B_e cover the whole graph.
    """
    Sinv = [I[g] for g in S]
    total = 0
    for start_a in (True, False):
        seen_a = bytearray(N)
        seen_b = bytearray(N)
        if start_a:
            seen_a[0] = 1
            fa, fb = [0], []
            ca, cb = 1, 0
        else:
            seen_b[0] = 1
            fa, fb = [], [0]
            ca, cb = 0, 1
        for _ in range(D):
            if not fa and not fb:
                break
            nb = []
            for x in fa:
                row = T[x]
                for g in S:
                    y = row[g]
                    if not seen_b[y]:
                        seen_b[y] = 1
                        nb.append(y)
            na = []
            for y in fb:
                row = T[y]
                for h in Sinv:
                    x = row[h]
                    if not seen_a[x]:
                        seen_a[x] = 1
                        na.append(x)
            ca += len(na)
            cb += len(nb)
            fa, fb = na, nb
        total += (N - ca) + (N - cb)
    return total


def _find(N, d, D, rng, steps, specs, deadline):
    """Local search over connection sets S (containing identity 0) for each group spec."""
    for spec in specs:
        if time.monotonic() >= deadline:
            return None
        order, mul, inv = _make(spec)
        T, I = _table(order, mul, inv)
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(S, T, I, N, D)
        for _ in range(steps):
            if cur == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(1, d)
            g = rng.randrange(1, N)
            if g in S:
                continue
            S2 = S[:]
            S2[i] = g
            c2 = _cost(S2, T, I, N, D)
            if c2 <= cur:
                S, cur = S2, c2
        if cur == 0:
            return spec, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2
    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    upper = lib.moore_bound(d, D) // 2
    N = max(d + 1, lib.moore_bound(d, D) // 10)
    fails = 0
    while time.monotonic() < deadline and fails < 6 and N <= upper:
        specs = _specs(N)
        cyc = [s for s in specs if s[0] == "c"]
        others = [s for s in specs if s[0] == "s"]
        chosen = cyc + rng.sample(others, min(3, len(others)))
        found = _find(N, d, D, rng, 300, chosen, deadline)
        if found is not None:
            spec, S = found
            order, mul, _ = _make(spec)
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                fails = 0
            else:
                fails += 1
        else:
            fails += 1
        N += 1
    return best
