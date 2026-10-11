import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------
# Multi-orbit voltage lifts with d random permutation layers.
#
# Base graph: k "A" vertices and k "B" vertices. Layer t is a permutation
# sigma_t of range(k); it contributes the dart (A_i, B_{sigma_t(i)}, g_{t,i}).
# Every A and B base vertex then has base degree d, so the lift over a group G
# of order N is a bipartite graph of order 2kN with max degree d. For k = 1
# this is the usual two-vertex Cayley lift (a difference cover of size d).
# Here we anneal the voltages directly on lib.bad_pairs (diameter 3 defects),
# over possibly non-abelian groups, for several k at once.
# ------------------------------------------------------------------

def _mul_options(N, rng):
    """Multiplication functions for several groups of order N."""
    muls = [lib.cyclic_group(N)[1]]
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                muls.append(lib.semidirect_group(m, k, r)[1])
            except ValueError:
                pass
    s = math.isqrt(N)
    if s > 1 and s * s == N:
        m = s
        muls.append(lambda x, y, m=m: ((x // m + y // m) % m) * m + (x % m + y % m) % m)
    return muls


def _configs(lo, hi, d, rng, cap):
    """(order, k, N, mul) candidates with lo <= 2kN <= hi, smallest order first."""
    out = []
    for k in range(1, 7):
        n_min = -(-lo // (2 * k))
        n_max = hi // (2 * k)
        for N in range(max(2, n_min), n_max + 1):
            for mul in _mul_options(N, rng):
                out.append((2 * k * N, k, N, mul))
    out.sort(key=lambda c: c[0])
    return out[:cap]


def _search(k, N, mul, d, rng):
    """Generator: anneal voltages until bad_pairs == 0. Yields None periodically,
    then (n, edges) when a valid lift is found."""
    pairs = [(t, i) for t in range(d) for i in range(k)]
    while True:
        perms = [rng.sample(range(k), k) for _ in range(d)]
        volt = {p: rng.randrange(N) for p in pairs}

        def edges_of():
            darts = [(i, k + perms[t][i], volt[(t, i)]) for (t, i) in pairs]
            return lib.group_lift(2 * k, darts, N, mul)

        cur_n, cur_e = edges_of()
        cost = lib.bad_pairs(cur_n, cur_e, 3)
        best_run = cost
        stall = 0
        T = 1.5
        for step in range(400000):
            if cost == 0:
                break
            if step % 20 == 0:
                yield None
            p = pairs[rng.randrange(len(pairs))]
            old = volt[p]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[p] = new
            n2, e2 = edges_of()
            c = lib.bad_pairs(n2, e2, 3)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
                cur_n, cur_e = n2, e2
                if c < best_run:
                    best_run = c
                    stall = 0
                else:
                    stall += 1
            else:
                volt[p] = old
                stall += 1
            if stall > 3000:
                break
        if cost == 0:
            yield (cur_n, cur_e)
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.75 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n + 1
    hi = lib.moore_bound(d, 3)
    if lo > hi:
        return base_n, base_e

    cfgs = _configs(lo, hi, d, rng, cap=80)
    active = []
    for order, k, N, mul in cfgs:
        active.append([order, _search(k, N, mul, d, rng)])

    best = None
    best_n = base_n
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            order, gen = entry
            if order <= best_n:
                active.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            active.remove(entry)
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                break
        active = [e for e in active if e[0] > best_n]

    if best is not None:
        return best
    return base_n, base_e
