import math
import random
import time

import lib


def _groups(N):
    """All (m, k, r) with Z_m x|_r Z_k of order N = m*k, where r^k = 1 mod m and gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group(m, k, r):
    """Return (order, mul, inv) for the group described by (m, k, r); identity is element 0."""
    if k == 1:
        return lib.cyclic_group(m)
    return lib.semidirect_group(m, k, r)


def _screen(N, mul, inv, S, D):
    """Cayley bipartite graph on A = G x {0}, B = G x {1}, edges (x, A)-(x*s, B) for s in S.

    Left multiplication is an automorphism that is transitive on each side, so BFS from
    (e, A) and (e, B) decides whether the diameter is at most D.
    """
    invS = [inv(s) for s in S]
    for start in (0, N):
        seen = bytearray(2 * N)
        seen[start] = 1
        frontier = [start]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    nb = [N + mul(v, s) for s in S]
                else:
                    y = v - N
                    nb = [mul(y, si) for si in invS]
                for w in nb:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            frontier = nxt
            cnt += len(nxt)
            if not frontier:
                break
        if cnt != 2 * N:
            return False
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))

    if d <= 0 or D <= 0:
        return 1, []

    # Trivial baseline: K_{d,d} (diameter 2).
    best = (1, [])
    kn = lib.haar_graph(d, range(d))
    if lib.is_valid(kn[0], kn[1], d, D):
        best = kn

    # Exact optimum for D = 3 when d-1 is a prime power.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    N = max(d, best[0] // 2 + 1)
    consecutive_fail = 0
    TRIAL_BUDGET = 250
    MAX_FAILS = 4

    # Search Cayley bipartite graphs of ascending group order N (2N vertices).
    while time.monotonic() < deadline and consecutive_fail < MAX_FAILS:
        groups = _groups(N)
        found = None
        trials = 0
        while (trials < TRIAL_BUDGET and time.monotonic() < deadline
               and found is None and groups):
            trials += 1
            m, k, r = groups[rng.randrange(len(groups))]
            order, mul, inv = _group(m, k, r)
            S = [0] + rng.sample(range(1, order), d - 1)
            if _screen(order, mul, inv, S, D):
                n = 2 * order
                edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
                if lib.is_valid(n, edges, d, D):
                    found = (n, edges)
        if found is not None:
            if found[0] > best[0]:
                best = found
            consecutive_fail = 0
        else:
            consecutive_fail += 1
        N += 1

    return best
