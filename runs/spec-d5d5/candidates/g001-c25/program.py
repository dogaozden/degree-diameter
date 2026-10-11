import math
import random
import time

import lib

MAX_GROUPS = 8   # groups prepared per order N
ROUNDS = 2       # round-robin passes over the prepared groups
ITERS = 120      # hill-climb steps per attempt


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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart, WLOG) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

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
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            prepared.append((T, invs))

        found = None
        for _ in range(ROUNDS):
            for T, invs in prepared:
                if time.monotonic() > deadline:
                    break
                S = _climb(N, T, invs, d, D, rng, ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found or time.monotonic() > deadline:
                break

        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D) and 2 * N > best[0]:
                best = (2 * N, edges)
        N += 1

    return best
