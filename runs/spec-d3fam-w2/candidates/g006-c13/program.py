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


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# giving order 2|G| with |G| <= d(d-1)+1.
#
# New in this version: a greedy "coverage-maximising" start. Instead of a
# uniformly random initial set, we grow S one element at a time, each time
# adding the candidate that covers the most still-uncovered ratios. Such
# starts land much closer to a full cover, so the annealer needs far fewer
# steps. Restarts alternate between greedy and random starts for diversity.


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
        for r in rs[:12]:
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


def _greedy_start(N, R, d, rng, pool=48):
    """Grow a d-element set S by greedy coverage of the ratio set.

    At each step, sample a pool of candidates outside S and add the one whose
    new ratios x*s^{-1} and s*x^{-1} (s in S) cover the most uncovered group
    elements. Ties are broken randomly.
    """
    S = [rng.randrange(N)]
    inS = set(S)
    covered = {R[S[0]][S[0]]}
    while len(S) < d:
        cands = [x for x in range(N) if x not in inS]
        if len(cands) > pool:
            cands = rng.sample(cands, pool)
        best, best_gain = None, -1
        for x in cands:
            gains = {R[x][x]}
            for s in S:
                gains.add(R[x][s])
                gains.add(R[s][x])
            gain = len(gains - covered)
            if gain > best_gain or (gain == best_gain and rng.random() < 0.5):
                best, best_gain = x, gain
        S.append(best)
        inS.add(best)
        for s in S[:-1]:
            covered.add(R[best][s])
            covered.add(R[s][best])
        covered.add(R[best][best])
    return S


def _random_start(N, d, rng):
    return rng.sample(range(N), d)


def _anneal(N, mul, inv, d, rng):
    """Generator: incremental annealing for d elements S with S S^{-1} = G.

    Yields None periodically (so the driver can round-robin many groups) and
    yields the cover S once found. Restarts alternate between greedy-coverage
    starts and uniformly random starts when a run stalls.
    """
    R = _ratio_table(N, mul, inv)
    restart = 0
    while True:
        if restart % 2 == 0:
            S = _greedy_start(N, R, d, rng)
        else:
            S = _random_start(N, d, rng)
        restart += 1
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        cost = zeros
        steps = 200000
        for step in range(steps):
            if cost == 0:
                break
            if step % 2000 == 0:
                yield None
            # Slowly cooling temperature; decreasing acceptance of uphill moves.
            T = max(0.05, 0.5 * (1.0 - step / steps))
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


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
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

    # Each active entry: [N, mul, gen]. Larger groups are tried first.
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            gen = _anneal(N, mul, inv, d, rng)
            active.append([N, mul, gen])

    best = None
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
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]

    if best is not None:
        return best
    return base_n, base_e
