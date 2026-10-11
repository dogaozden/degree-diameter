import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline graphs used when the search does not improve on them."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))            # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)      # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Diameter is at most 3 when
# S S^{-1} = G, so we need a "difference cover" of size d in a group G of
# order N, giving order 2N with N <= d(d-1)+1.

def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k."""
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
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving e.

    Pairs are (e,e), (e,o), (o,e) for o in others. Returns the change in the
    number of uncovered group elements (zeros of cnt).
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
    """Generator: annealing for d elements S with S S^{-1} = G.

    Yields None periodically so a driver can round-robin many groups, and
    yields the cover S once found. Each run is a geometric cooling schedule;
    a stalled run restarts from a fresh random set.
    """
    R = _ratio_table(N, mul, inv)
    steps = 60000
    T0, T1 = 1.0, 0.05
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        for step in range(steps):
            if zeros == 0:
                break
            if step % 2000 == 0:
                yield None
            T = T0 * (T1 / T0) ** (step / steps)
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            dz = _pair_update(cnt, R, old, others, -1)
            dz += _pair_update(cnt, R, x, others, 1)
            if dz <= 0 or rng.random() < math.exp(-dz / T):
                zeros += dz
                S[i] = x
                inS.discard(old)
                inS.add(x)
            else:
                _pair_update(cnt, R, x, others, -1)
                _pair_update(cnt, R, old, others, 1)
        if zeros == 0:
            yield list(S)
            return


# ---------------------------------------------------------------- driver

def _search_difference_lifts(d, D, best_n, deadline, rng, consider_fn):
    """Round-robin annealing over (N, group) pairs, largest N first.

    Calls consider_fn(n, edges) on each valid lift. Returns the best order
    found (or best_n if nothing better was found).
    """
    lo = best_n // 2 + 1          # need 2N > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return best_n

    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            gen = _anneal(N, mul, inv, d, rng)
            active.append([N, mul, gen])

    best_N = lo - 1
    found_n = best_n
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
            active.remove(entry)
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            if n > found_n and lib.is_valid(n, edges, d, D):
                consider_fn(n, edges)
                found_n = n
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return found_n


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base = _fallback(d, D)
    if not lib.is_valid(base[0], base[1], d, D):
        return 1, []
    best = base
    best_n = base[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only the diameter-3 regime is searched. Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return best

    # Araujo-Pardo & Lopez record family, used as a starting point.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover Haar lifts: search for graphs beating the current best.
    try:
        _search_difference_lifts(d, D, best_n, deadline, rng, consider)
    except Exception:
        pass

    return best
