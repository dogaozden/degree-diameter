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
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ phase 1: difference covers

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect Z_m x| Z_k."""
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
        for r in rs[:6]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    change = 0
    row = R[e]
    gs = [row[e]] + [row[o] for o in others] + [R[o][e] for o in others]
    if sign > 0:
        for g in gs:
            if cnt[g] == 0:
                change -= 1
            cnt[g] += 1
    else:
        for g in gs:
            cnt[g] -= 1
            if cnt[g] == 0:
                change += 1
    return change


def _anneal(N, mul, inv, d, rng):
    """Generator: incremental annealing for d elements S with S S^{-1} = G."""
    R = _ratio_table(N, mul, inv)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        cost = zeros
        T = 0.5
        for step in range(200000):
            if cost == 0:
                break
            if step % 2000 == 0:
                yield None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            zeros += _pair_update(cnt, R, old, others, -1)
            zeros += _pair_update(cnt, R, x, others, 1)
            if zeros <= cost or rng.random() < math.exp(-(zeros - cost) / T):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                cost = zeros
            else:
                zeros += _pair_update(cnt, R, x, others, -1)
                zeros += _pair_update(cnt, R, old, others, 1)
        if cost == 0:
            yield list(S)
            return


def _difference_cover_search(d, base_n, deadline, rng):
    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            gen = _anneal(N, mul, inv, d, rng)
            active.append([N, mul, gen])

    best = None
    best_n = base_n
    best_N = lo - 1
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            N, mul, gen = entry
            if N <= best_N:
                active.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            active.remove(entry)
            if n > best_n and lib.is_valid(n, edges, d, D_GLOBAL[0]):
                best = (n, edges)
                best_n = n
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# --------------------------------- phase 2: random multi-vertex group lifts
#
# Base graph: k A-vertices and k B-vertices, each of degree d, formed by d
# random perfect matchings between A and B, each dart carrying a random
# voltage in a (possibly non-abelian) group of order N. The lift has 2kN
# vertices and max degree <= d by construction. Candidates are checked
# exactly with lib.is_valid, so an invalid graph is never returned.

def _voltage_search(d, D, best_n, deadline, rng):
    moore = lib.moore_bound(d, D)
    best = None
    tries = 0
    while time.monotonic() < deadline:
        tries += 1
        k = rng.choice((2, 2, 3))
        lo_N = best_n // (2 * k) + 1
        hi_N = moore // (2 * k)
        if lo_N > hi_N:
            k = 2
            lo_N = best_n // 4 + 1
            hi_N = moore // 4
            if lo_N > hi_N:
                break
        N = rng.randint(lo_N, hi_N)
        groups = _group_list(N, rng)
        _order, mul, _inv = rng.choice(groups)

        darts = []
        for _ in range(d):
            perm = list(range(k))
            rng.shuffle(perm)
            for i in range(k):
                darts.append((i, k + perm[i], rng.randrange(N)))
        n, edges = lib.group_lift(2 * k, darts, N, mul)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best


D_GLOBAL = [3]


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)
    D_GLOBAL[0] = D

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = None
    best_n = base_n

    # Phase 1: classic Cayley difference-cover search (known strong family).
    p1 = _difference_cover_search(d, base_n, start + 0.4 * budget, rng)
    if p1 is not None and p1[0] > best_n:
        best = p1
        best_n = p1[0]

    # Phase 2: bold move, random 2- and 3-vertex-per-side group lifts
    # over arbitrary groups, aiming to exceed the best order so far.
    p2 = _voltage_search(d, D, best_n, deadline, rng)
    if p2 is not None and p2[0] > best_n:
        best = p2
        best_n = p2[0]

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
