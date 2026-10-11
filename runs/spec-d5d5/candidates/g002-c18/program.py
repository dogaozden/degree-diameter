import math
import random
import time

import lib

ANNEAL_ITERS = 3000   # annealing steps per group attempt
T0 = 2.0              # starting temperature (in units of unreached pairs)
T_FLOOR = 0.05


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when k = 1)."""
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
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism
    of each side, so eccentricities of A_0 and B_0 determine the diameter.
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
    """Simulated annealing over a connection set S (identity fixed as element 0, WLOG).

    Returns S with zero unreached pairs, or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best = cur
    best_S = S[:]
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(T_FLOOR, T0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            if cur < best:
                best = cur
                best_S = S[:]
        else:
            S[i] = old
    return best_S if best == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Baseline: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record constructions for D = 3.
    if D == 3:
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass

    if d < 2 or D < 2:
        return best

    rng = random.Random(seed)
    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    N = max(d + 1, best[0] // 2 + 1)

    while N <= Nmax and time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        remaining = deadline - time.monotonic()
        attempt_end = min(deadline, time.monotonic() + max(2.0, 0.25 * remaining))

        tables = {}
        found = None
        tries = 0
        while found is None and time.monotonic() < attempt_end and groups:
            gi = tries % len(groups)
            tries += 1
            if gi not in tables:
                m, k, r = groups[gi]
                _, mul, inv = lib.semidirect_group(m, k, r)
                T = [[mul(x, g) for g in range(N)] for x in range(N)]
                invs = [inv(g) for g in range(N)]
                tables[gi] = (T, invs)
            T, invs = tables[gi]
            S = _anneal(N, T, invs, d, D, rng, ANNEAL_ITERS, attempt_end)
            if S is not None:
                found = (T, S)

        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D) and 2 * N > best[0]:
                best = (2 * N, edges)
            N += 1   # success: push the order up
        # On failure, stay at N and retry with fresh randomness.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
