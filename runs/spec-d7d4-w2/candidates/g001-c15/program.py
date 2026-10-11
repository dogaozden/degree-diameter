import math
import random
import time
import lib


def _cover_cost(m, S, D):
    """Number of vertices of the Haar graph H(m, S) NOT within distance D of a_0 or b_0.

    By the symmetries of the Haar graph (translations and the side swap a_i <-> b_{-i}),
    diameter <= D holds iff both balls of radius D around a_0 and b_0 cover everything.
    """
    total = 0
    for side in (0, 1):
        seen_a = bytearray(m)
        seen_b = bytearray(m)
        if side == 0:
            seen_a[0] = 1
            fa, fb = [0], []
        else:
            seen_b[0] = 1
            fa, fb = [], [0]
        for _ in range(D):
            na, nb = [], []
            for i in fa:
                for s in S:
                    j = (i + s) % m
                    if not seen_b[j]:
                        seen_b[j] = 1
                        nb.append(j)
            for j in fb:
                for s in S:
                    i = (j - s) % m
                    if not seen_a[i]:
                        seen_a[i] = 1
                        na.append(i)
            fa, fb = na, nb
        total += 2 * m - sum(seen_a) - sum(seen_b)
    return total


def _anneal(m, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (size d, containing 0) of Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _cover_cost(m, S, D)
    T = 2.0
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
        k = rng.randrange(1, d)
        v = rng.randrange(1, m)
        if v in S:
            continue
        cand = S[:]
        cand[k] = v
        c = _cover_cost(m, cand, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = cand, c
        T = max(0.05, T * 0.999)
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if D == 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    # Always-valid fallback: K_{d,d} (diameter 2 <= D).
    best = lib.haar_graph(d, range(d))
    best_m = d
    if d < 2:
        return best

    upper = max(d + 1, lib.moore_bound(d, D) // 2)
    m = d + 1
    consecutive_fail = 0
    attempts_at_m = 0
    while time.monotonic() < deadline and m <= upper and consecutive_fail < 8:
        S = _anneal(m, d, D, rng, 4000, deadline)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_m = m
            m += 1
            consecutive_fail = 0
            attempts_at_m = 0
        else:
            attempts_at_m += 1
            if attempts_at_m >= 3:
                m += 1
                attempts_at_m = 0
                consecutive_fail += 1

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
