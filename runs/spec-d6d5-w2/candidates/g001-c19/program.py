import random
import time

import lib


def _groups(N):
    """All semidirect products Z_m x| Z_k of order N, as (m, k, r) with r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        rs = [0] if m == 1 else range(1, m)
        for r in rs:
            if m > 1 and not _coprime(r, m):
                continue
            if pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _coprime(a, b):
    while b:
        a, b = b, a % b
    return a == 1


def _bicayley_ok(N, S, mul, inv, D):
    """Check the bi-Cayley graph A_x ~ B_{x*s} (s in S) has diameter <= D.

    Left multiplication is an automorphism that is transitive on each side, so it is
    enough that the eccentricities of A_0 and B_0 are both <= D (and both connected).
    """
    sinv = [inv(s) for s in S]
    adjA = [[mul(x, s) for s in S] for x in range(N)]     # A_x -> B indices
    adjB = [[mul(y, si) for si in sinv] for y in range(N)]  # B_y -> A indices
    total = 2 * N

    def reach_all(src):
        seen = bytearray(total)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    nb = [N + v for v in adjA[u]]
                else:
                    nb = adjB[u - N]
                for w in nb:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        return count == total

    return reach_all(0) and reach_all(N)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # Optimal D = 3 construction when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe baseline.
    best = lib.haar_graph(d, range(d))  # K_{d,d}
    if not lib.is_valid(2 * d, best[1], d, D):
        best = (2, [(0, 1)])
    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    best_N = best[0] // 2
    N = max(best_N + 1, d)
    attempts_per_N = 400

    while time.monotonic() < deadline:
        groups = _groups(N)
        found = None
        if groups:
            for _ in range(attempts_per_N):
                if time.monotonic() >= deadline:
                    break
                m, k, r = rng.choice(groups)
                _, mul, inv = lib.semidirect_group(m, k, r)
                S = [0] + rng.sample(range(1, N), d - 1)  # identity WLOG in S
                if _bicayley_ok(N, S, mul, inv, D):
                    found = (S, mul)
                    break
        if found is not None:
            S, mul = found
            edges = [(x, N + mul(x, s)) for x in range(N) for s in S]
            if lib.is_valid(2 * N, edges, d, D):
                best = (2 * N, edges)
        N += 1

    return best
