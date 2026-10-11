import math
import random
import time

import lib


def _groups(N, rng):
    """Multiplication/inverse pairs for semidirect groups Z_m x| Z_k with m*k = N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            rs = [0]
        else:
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if len(rs) > 4:
                rs = rng.sample(rs, 4)
        for r in rs:
            try:
                _, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            out.append((mul, inv))
    return out


def _ok(N, mul, inv, S, D):
    """Check diameter <= D of the bipartite Cayley graph A_x ~ B_{x*g}, g in S.

    Left translation acts transitively on each side, so BFS from A_identity
    and B_identity decides the diameter.
    """
    Sinv = [inv(g) for g in S]
    total = 2 * N
    for start in (0, N):
        seen = [False] * total
        seen[start] = True
        frontier = [start]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for g in S:
                        w = N + mul(v, g)
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
                else:
                    y = v - N
                    for gi in Sinv:
                        w = mul(y, gi)
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        if count != total:
            return False
    return True


def _search_order(N, d, D, groups, rng, budget_end):
    """Random search over connection sets of size d, round-robin over groups."""
    if not groups:
        return None
    tries = 0
    while tries < 3 or time.monotonic() < budget_end:
        mul, inv = groups[tries % len(groups)]
        tries += 1
        S = rng.sample(range(N), d)
        if _ok(N, mul, inv, S, D):
            return S, mul
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    moore = lib.moore_bound(d, D)
    hi = min(max(d, moore // 2), 2000)
    lo = min(max(d, moore // 8), hi)

    rng = random.Random(seed)
    N = hi
    while N >= lo and time.monotonic() < deadline:
        now = time.monotonic()
        remaining_n = N - lo + 1
        budget_end = now + (deadline - now) / remaining_n
        groups = _groups(N, rng)
        found = _search_order(N, d, D, groups, rng, budget_end)
        if found:
            S, mul = found
            edges = [(x, N + mul(x, g)) for x in range(N) for g in S]
            n = 2 * N
            if lib.is_valid(n, edges, d, D):
                return n, edges
        N -= 1
    return fallback
