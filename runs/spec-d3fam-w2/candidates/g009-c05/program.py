import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: Moore-extremal PG(2,q), the Araujo-Lopez record family,
# and K_{d,d} (diameter 2). All are verified before use.
# ----------------------------------------------------------------------------

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
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                return lib.projective_plane_incidence(q)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over groups of order N.
#
# Two base vertices a, b with darts (a, b, s), s in S, give the bipartite graph
# on G x {0,1} with a_x ~ b_{x s}. Every vertex has degree |S| = d. Diameter is
# at most 3 whenever S S^{-1} = G (a "difference cover"), giving order 2N with
# N <= d(d-1)+1. We search for such covers with incremental simulated
# annealing over several groups of each order, round-robin, favouring larger N.
# ----------------------------------------------------------------------------

def _group_list(N, rng, per_N=3):
    """Cyclic group of order N plus up to per_N semidirect products Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    specs = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    rng.shuffle(specs)
    for m, k, r in specs[:per_N]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving element e.

    Returns the change in the number of zero entries of cnt.
    """
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
    """Generator: incremental annealing for d elements S with S S^{-1} = G.

    Yields None periodically so the driver can round-robin many groups, and
    yields the cover S once found. Restarts from a fresh random state if a
    run stalls.
    """
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


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 6.0)
    deadline = start + max(1.0, budget)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    best = None
    best_N = lo - 1
    try:
        # Each active entry: [N, mul, inv, generator]. Larger orders first.
        active = []
        for N in range(hi, lo - 1, -1):
            if N < d:
                continue
            for _order, mul, inv in _group_list(N, rng):
                active.append([N, mul, inv, _anneal(N, mul, inv, d, rng)])

        while active and time.monotonic() < deadline:
            for entry in list(active):
                if time.monotonic() >= deadline:
                    break
                N, mul, inv, gen = entry
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
                active.remove(entry)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
                cur = best[0] if best is not None else base_n
                if n > cur and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = N
                    active = [e for e in active if e[0] > best_N]
                    break
            active = [e for e in active if e[0] > best_N]
    except Exception:
        pass

    if best is not None and best[0] > base_n and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
