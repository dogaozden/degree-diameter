import math
import random
import time

import lib

# Bold change for D >= 3: bipartite Haar graphs H(Z_m, S) with |S| = d whose
# difference set S - S covers all of Z_m. Then every same-side pair is joined by a
# path of length 2 (a_i - b_{i+s} - a_{i+s-s'}), and every opposite-side pair by a
# path of length 1 or 3 (since y = j - i - s3 lies in S - S for any fixed s3 in S).
# So diameter <= 3 with 2m vertices and degree d. Searching for the largest m with
# a difference cover of size d beats the projective-plane-based records at d = 16.
# The K_{d,d} and PG(2,q) incidence graphs are kept as always-valid fallbacks.


def _uncovered(m, S):
    """Number of residues in Z_m missing from the difference set S - S."""
    seen = bytearray(m)
    for a in S:
        for b in S:
            seen[(a - b) % m] = 1
    return m - sum(seen)


def _find_cover(m, k, rng, deadline, iters):
    """Simulated annealing for a k-subset S of Z_m (0 in S) with S - S = Z_m. None on failure."""
    if k > m or k < 2:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    c = _uncovered(m, S)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        T = 0.6 * (0.02 ** (it / iters))
        i = rng.randrange(1, k)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _uncovered(m, S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Projective plane incidence graph (diameter 3) as a second baseline.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                break

        # Main family: Haar graphs from difference covers of size d.
        k = d
        if k >= 2:
            upper = k * (k - 1) + 1  # counting bound on m
            rng2 = random.Random(seed * 1000003 + d * 31 + D)

            def attempt(m, until):
                S = _find_cover(m, k, rng2, min(deadline, until), 60000)
                if S is None:
                    return False
                n, e = lib.haar_graph(m, S)
                consider(n, e)
                return True

            # Ascending sweep from a comfortably achievable size.
            m = max(k + 1, upper // 2)
            best_m = 0
            fails = 0
            while m <= upper and time.monotonic() < deadline:
                if attempt(m, time.monotonic() + 3.0):
                    best_m = m
                    fails = 0
                else:
                    fails += 1
                    if fails >= 3:
                        break
                m += 1

            # Frontier: keep retrying just above the best size found.
            while time.monotonic() < deadline:
                t = max(best_m + 1, k + 1)
                if rng2.random() < 0.3:
                    t += 1
                if t > upper:
                    break
                if attempt(t, time.monotonic() + 4.0):
                    best_m = max(best_m, t)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
