import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: bitset cyclic bi-Cayley cost.
# Graph on A_0..A_{N-1}, B_0..B_{N-1} with A_x ~ B_{x+g} for g in S (Z_N).
# Sets of reached vertices are Python ints; one expansion step is a rotation
# of an N-bit integer per connection element. This is ~50x faster than BFS
# over adjacency lists, so the annealer can afford many more moves.
# Translation is an automorphism, so BFS from A_0 and B_0 suffices.
# ----------------------------------------------------------------------------

def _rot(X, g, N, full):
    """Bit x -> bit (x + g) mod N for every set bit x of X (g in [0, N))."""
    if g == 0:
        return X
    return ((X << g) | (X >> (N - g))) & full


def _cyc_cost(N, Sn, Sh, D, full):
    """Unreached (source, vertex) pairs within distance D from A_0 and from B_0.

    Sn = S, Sh = [(-g) % N for g in S]. Zero means diameter <= D.
    """
    total = 0
    for side in (0, 1):
        seenA = 1 if side == 0 else 0
        seenB = 0 if side == 0 else 1
        fa, fb = seenA, seenB
        for _ in range(D):
            nb = 0
            for g in Sn:
                nb |= _rot(fa, g, N, full)
            nb &= ~seenB & full
            na = 0
            for h in Sh:
                na |= _rot(fb, h, N, full)
            na &= ~seenA & full
            seenB |= nb
            seenA |= na
            fa, fb = na, nb
            if not (fa or fb):
                break
        total += 2 * N - seenA.bit_count() - seenB.bit_count()
    return total


def _cyc_anneal(N, d, D, rng, deadline, iters):
    """Annealing over connection sets S of Z_N with 0 fixed in S (WLOG). Returns S or None."""
    full = (1 << N) - 1

    def cost_of(S):
        return _cyc_cost(N, S, [(N - g) % N for g in S], D, full)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost_of(S)
    best, bestS = cur, list(S)
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if best == 0:
            break
        if (step & 255) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.15, T0 * (1.0 - step / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = cost_of(S2)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best:
                best, bestS = cur, list(S)
    return bestS if best == 0 else None


# ----------------------------------------------------------------------------
# Non-cyclic semidirect bi-Cayley lifts (table-based, as in the parent).
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _gen_unreached(N, T, invs, S, D):
    """Unreached pairs from A_0 and B_0 for the bi-Cayley graph A_x ~ B_{x g}, g in S."""
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


def _gen_climb(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _gen_unreached(N, T, invs, S, D)
    best, bestS = cur, list(S)
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if best == 0 or time.monotonic() > deadline:
            break
        temp = max(0.15, T0 * (1.0 - step / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = _gen_unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best:
                best, bestS = cur, list(S)
    return bestS if best == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

CYC_ITERS = 12000
GEN_ITERS = 800


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if 2 * lo > moore:
            break

        if rng.random() < 0.8 and lo > d:
            # Cyclic bi-Cayley lift with the fast bitset cost.
            N = lo + rng.randrange(max(1, lo // 25))
            if 2 * N > moore or N <= d:
                N = lo
            now = time.monotonic()
            slice_end = now + max(0.4, 0.12 * (deadline - now))
            S = _cyc_anneal(N, d, D, rng, min(deadline, slice_end), CYC_ITERS)
            if S is not None:
                consider(2 * N, [(x, N + (x + g) % N) for x in range(N) for g in S])
        else:
            # Non-cyclic semidirect bi-Cayley lift.
            N = lo + rng.randrange(max(1, lo // 25))
            groups = [g for g in _groups(N) if g[1] >= 2]
            if groups and 2 * N <= moore and N > d:
                m, k2, r = rng.choice(groups)
                order, T, invs = _tables(m, k2, r)
                S = _gen_climb(order, T, invs, d, D, rng, GEN_ITERS, deadline)
                if S is not None:
                    consider(2 * order,
                             [(x, order + T[x][g]) for x in range(order) for g in S])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
