import math
import random
import time

import lib

MAX_GROUPS = 8     # groups prepared per order N
ITERS = 400        # annealing steps per attempt
FRAC_PER_N = 0.2   # share of remaining time one order N may consume
TIME_FRAC = 0.8    # fraction of time_limit used before returning


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when r = 1, k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism,
    so checking eccentricity from A_0 and B_0 suffices for the whole graph.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (identity fixed as one dart, WLOG).

    Minimises the number of unreached pairs; accepts uphill moves with a
    temperature that cools linearly, so the search can leave local minima.
    Returns a zero-cost S or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_v, best_S = cur, S[:]
    for it in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
            if cur < best_v:
                best_v, best_S = cur, S[:]
    return best_S if best_v == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    N = d + 1
    while N <= Nmax and time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        prepared = []
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            prepared.append((T, invs))

        # Per-order budget: a fraction of what remains, so large N still get time.
        now = time.monotonic()
        n_deadline = min(deadline, now + max(0.5, FRAC_PER_N * (deadline - now)))

        found = None
        attempt = 0
        while prepared and found is None and time.monotonic() < n_deadline:
            T, invs = prepared[attempt % len(prepared)]
            attempt += 1
            S = _anneal(N, T, invs, d, D, rng, ITERS, n_deadline)
            if S is not None:
                found = (T, S)

        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D) and 2 * N > best[0]:
                best = (2 * N, edges)
        N += 1

    return best
