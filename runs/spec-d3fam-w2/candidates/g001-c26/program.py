import math
import random
import time

import lib


def _fallback(d, D):
    """Verified-by-construction graphs used as the starting point."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))              # K_{d,d}, optimal for D = 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 when
# S S^{-1} = G, so the task is a difference cover of size d in a group G,
# giving order 2|G|.

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus a few semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _search(N, R, d, rng, steps, deadline):
    """Annealing search for d distinct elements S with S S^{-1} = G."""
    S = rng.sample(range(N), d)

    def uncovered(S):
        return N - len({R[a][b] for a in S for b in S})

    cost = uncovered(S)
    T = 0.6
    for _ in range(steps):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = uncovered(S)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _cayley_search(d, D, rng, deadline, base_n):
    """Search for a larger difference-cover lift. Returns (n, edges) or None."""
    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # difference-cover bound
    if lo > hi:
        return None

    jobs = []                     # (N, mul, inv); R tables built per use, freed after
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            jobs.append((N, mul, inv))

    best = None
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        jobs = [j for j in jobs if j[0] > best_N]
        rng.shuffle(jobs)
        for N, mul, inv in list(jobs):
            if time.monotonic() >= deadline:
                break
            if N <= best_N:
                continue
            R = _ratio_table(N, mul, inv)
            S = _search(N, R, d, rng, 2000, deadline)
            del R
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                break
    return best


# ------------------------------------------------ Haar-graph search (general D)

def _haar_search(d, D, rng, deadline, base_n):
    """Random Haar graphs of growing order; returns (n, edges) or None."""
    best = None
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if n > base_n and lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Cases where the base graph is already optimal or no search applies.
    if D <= 2 or d <= 2:
        return base_n, base_e
    if D == 3 and lib.is_prime_power(d - 1):
        return base_n, base_e

    if D == 3:
        res = _cayley_search(d, D, rng, deadline, base_n)
    else:
        res = _haar_search(d, D, rng, deadline, base_n)

    if res is not None and res[0] > base_n and lib.is_valid(res[0], res[1], d, D):
        return res
    return base_n, base_e
