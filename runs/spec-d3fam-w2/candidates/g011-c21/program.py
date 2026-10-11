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


# ------------------------------------------------ group candidates

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


# ------------------------------------------- two-vertex difference covers

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

    Yields None periodically; yields the cover S once found.
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


def _two_search(d, base_n, rng, deadline):
    """Search 2|G|-vertex Cayley-type diameter-3 graphs. Returns (n, edges) or None."""
    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            active.append([N, mul, _anneal(N, mul, inv, d, rng)])

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
            if n > base_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ------------------------------------- four-vertex voltage lifts (new idea)
#
# Base graph: A0, A1 on one side, B0, B1 on the other, with a degree-d
# incidence pattern M = [[a, d-a], [d-a, a]]. Each base dart carries a voltage
# in a finite group G, giving a bipartite graph on 4|G| vertices. Voltages are
# annealed to minimise the number of vertex pairs at distance > 3 (computed
# exactly by lib.bad_pairs). Cost 0 means diameter <= 3.

def _lift4_anneal(N, mul, d, rng):
    """Generator: anneal voltages on the 4-vertex base. Yields None, then (n, edges) on success."""
    while True:
        a = rng.randint(1, d - 1)
        pairs = []
        for i in (0, 1):
            for j in (0, 1):
                m = a if i == j else d - a
                pairs += [(i, 2 + j)] * m
        volt = [rng.randrange(N) for _ in pairs]

        def evaluate(vs):
            darts = [(u, v, g) for (u, v), g in zip(pairs, vs)]
            n, edges = lib.group_lift(4, darts, N, mul)
            return lib.bad_pairs(n, edges, 3), n, edges

        cost, n, edges = evaluate(volt)
        T = 2.0
        for step in range(30000):
            if cost == 0:
                break
            yield None
            k = rng.randrange(len(volt))
            old = volt[k]
            volt[k] = rng.randrange(N)
            new_cost, n2, edges2 = evaluate(volt)
            if new_cost <= cost or rng.random() < math.exp(-(new_cost - cost) / T):
                cost, n, edges = new_cost, n2, edges2
            else:
                volt[k] = old
            T = max(0.05, T * 0.9998)
        if cost == 0:
            yield (n, edges)
            return


def _four_search(d, best_n, rng, deadline):
    """Search 4|G|-vertex voltage lifts beating best_n. Returns (n, edges) or None."""
    if d < 2:
        return None
    hi = lib.moore_bound(d, 3) // 4
    lo = best_n // 4 + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        groups = _group_list(N, rng)
        rng.shuffle(groups)
        for _order, mul, _inv in groups[:3]:
            active.append([N, mul, _lift4_anneal(N, mul, d, rng)])

    best = None
    cur = best_n
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            N, mul, gen = entry
            if 4 * N <= cur:
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
            if n > cur and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                cur = n
                active = [e for e in active if 4 * e[0] > cur]
                break
        active = [e for e in active if 4 * e[0] > cur]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best_n = base_n

    # Phase 1: two-vertex difference-cover search (the parent's route).
    r = _two_search(d, base_n, rng, start + 0.5 * budget)
    if r is not None and r[0] > best_n and lib.is_valid(r[0], r[1], d, D):
        best, best_n = r, r[0]

    # Phase 2: four-vertex voltage lifts over non-cyclic groups, using the rest of the time.
    if time.monotonic() < deadline:
        r = _four_search(d, best_n, rng, deadline)
        if r is not None and r[0] > best_n and lib.is_valid(r[0], r[1], d, D):
            best, best_n = r, r[0]

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
