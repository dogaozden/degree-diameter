import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold direction: bi-Cayley graphs over a wider family of finite groups.
#
# A bi-Cayley graph over a group G with connection set S (|S| = d, identity in S
# WLOG) has vertices A_x, B_x for x in G, and edges A_x -- B_{x g} for g in S.
# Left translation is an automorphism, so the diameter can be checked by BFS
# from A_0 and B_0 alone.
#
# Compared with the parent, this version:
#   * uses Heisenberg-type groups (order p^3 times a cyclic factor) and direct
#     products of metacyclic groups with cyclic groups, not only Z_m x| Z_k;
#   * replaces hill-climbing with simulated annealing on the number of unreached
#     (source, vertex) pairs;
#   * sweeps the group order N upward with a per-N time slice, and keeps the
#     largest validated graph.
# Safe fallback: K_{d,d} (diameter 2), replaced by any larger graph that passes
# lib.is_valid.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # group families tried per order N
ANNEAL_ITERS = 6000   # annealing steps per (group, N)
T_START = 3.0
T_END = 0.3
_CACHE = {}


def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _specs(N):
    """Group descriptors of order N: metacyclic Z_m x|_r Z_k times Z_c, and Heisenberg-type times Z_c."""
    out = []
    for c in _divisors(N):
        M = N // c
        for k in _divisors(M):
            m = M // k
            for r in range(m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append(('sd', m, k, r, c))
    for p in range(2, N + 1):
        if p ** 3 > N:
            break
        if N % (p ** 3) == 0 and all(p % q for q in range(2, int(p ** 0.5) + 1)):
            out.append(('heis', p, N // (p ** 3)))
    return out


def _group_mul(spec):
    """Return (order, mul) for a group descriptor. Identity is always coded as 0."""
    if spec[0] == 'sd':
        _, m, k, r, c = spec
        M, hm, _ = lib.semidirect_group(m, k, r)
    else:
        _, p, c = spec
        M = p ** 3

        def hm(x, y, p=p):
            # Heisenberg law: (a,b,e)(a',b',e') = (a+a', b+b', e+e'+a*b') mod p
            a1, b1, e1 = x // (p * p), (x // p) % p, x % p
            a2, b2, e2 = y // (p * p), (y // p) % p, y % p
            return ((a1 + a2) % p) * p * p + ((b1 + b2) % p) * p + (e1 + e2 + a1 * b2) % p
    if c == 1:
        return M, hm

    def mul(x, y):
        h1, z1 = divmod(x, c)
        h2, z2 = divmod(y, c)
        return hm(h1, h2) * c + (z1 + z2) % c

    return M * c, mul


def _tables(spec):
    """Cached (order, T, invs): T[x][g] = x*g, invs[g] = g^-1 (identity is 0, so inverse is the 0 entry of row g)."""
    hit = _CACHE.get(spec)
    if hit is not None:
        return hit
    N, mul = _group_mul(spec)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [row.index(0) for row in T]
    val = (N, T, invs)
    if len(_CACHE) >= 16:
        _CACHE.clear()
    _CACHE[spec] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs at distance > D, sources A_0 and B_0. Zero means diameter <= D."""
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
    """Simulated annealing for a connection set S of size d; returns S with zero unreached pairs, or None."""
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_cost = cur
    best_S = list(S)
    if cur == 0:
        return best_S
    if d < 2:
        return None
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_START * (T_END / T_START) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
            if cur < best_cost:
                best_cost = cur
                best_S = list(S)
                if cur == 0:
                    return best_S
        else:
            S[i] = old
    return best_S if best_cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and 2d vertices.
    best = (2 * d, lib.haar_graph(d, range(d))[1])
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Cheap structured baseline for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and d - 1 <= 40 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if n0 > best[0] and lib.is_valid(n0, e0, d, D):
            best = (n0, e0)

    # Sweep the group order N upward from the first order that could beat the current best.
    N = max(best[0] // 2 + 1, d)
    slice_len = max(1.0, 0.10 * budget)
    while N <= moore // 2 and time.monotonic() < deadline:
        specs = _specs(N)
        rng.shuffle(specs)
        slice_end = min(deadline, time.monotonic() + slice_len)
        found = None
        for spec in specs[:MAX_GROUPS]:
            if time.monotonic() >= slice_end:
                break
            NN, T, invs = _tables(spec)
            S = _anneal(N, T, invs, d, D, rng, ANNEAL_ITERS, slice_end)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if lib.is_valid(2 * N, edges, d, D) and 2 * N > best[0]:
                best = (2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, lib.haar_graph(d, range(d))[1])
    return best
