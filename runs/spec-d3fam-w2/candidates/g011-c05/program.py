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


# ------------------------------------------------------------ group helpers

def _group_candidates(N, rng, limit=6):
    """Groups of order N: the cyclic group plus random semidirect products Z_m x| Z_k."""
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
        for r in rs[:limit]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


# ------------------------------------------- phase 1: Cayley difference covers

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
    """Generator: annealing for d elements S with S S^{-1} = G.

    Yields None periodically and yields the cover S once found.
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


def _cayley_phase(d, D, rng, best, deadline, moore):
    """Parent-style search for 2|G| vertex difference covers. Returns the best (n, edges)."""
    base_n = best[0]
    lo = base_n // 2 + 1
    hi = min(d * (d - 1) + 1, moore // 2)
    if lo > hi:
        return best
    active = []  # entries: [max_n, N, mul, generator]
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_candidates(N, rng):
            active.append([2 * N, N, mul, _anneal(N, mul, inv, d, rng)])
    best_n = base_n
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            if entry[0] <= best_n:
                active.remove(entry)
                continue
            try:
                res = next(entry[3])
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            _, N, mul, _ = entry
            active.remove(entry)
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                active = [e for e in active if e[0] > best_n]
                break
        active = [e for e in active if e[0] > best_n]
    return best


# ------------------------------------ phase 2: multi-vertex voltage lifts

def _base_matrices(d, k):
    """Base multiplicity matrices with all row and column sums equal to d (connected)."""
    if k == 2:
        return [[[p, d - p], [d - p, p]] for p in range(1, d)]
    out = []
    for a in range(1, d):
        for b in range(1, d - a):
            c = d - a - b
            if c >= 1:
                out.append([[a, b, c], [c, a, b], [b, c, a]])
    return out


def _vl_cost(g, darts, k, N, mulT, invT):
    """Number of (fibre representative, vertex) pairs at distance > 3, plus duplicate penalty.

    Left multiplication is an automorphism of the lift, so one BFS per base vertex suffices.
    """
    nbA = [[] for _ in range(k)]
    nbB = [[] for _ in range(k)]
    for (i, j), gg in zip(darts, g):
        nbA[i].append((k + j, gg))
        nbB[j].append((i, invT[gg]))
    total = 3 * (len(darts) - len(set(zip(darts, g))))
    n = 2 * k * N
    for u in range(2 * k):
        seen = {u * N}
        frontier = [(u, 0)]
        for _ in range(3):
            nxt = []
            for b, x in frontier:
                row = mulT[x]
                if b < k:
                    for cb, gg in nbA[b]:
                        y = row[gg]
                        key = cb * N + y
                        if key not in seen:
                            seen.add(key)
                            nxt.append((cb, y))
                else:
                    for cb, gi in nbB[b - k]:
                        y = row[gi]
                        key = cb * N + y
                        if key not in seen:
                            seen.add(key)
                            nxt.append((cb, y))
            frontier = nxt
        total += n - len(seen)
    return total


def _vl_job(N, mul, inv, M, rng):
    """Generator: anneal voltages on the base multigraph M over a group of order N.

    Yields None periodically and finally yields (n, edges) of a diameter-3 lift.
    """
    k = len(M)
    mulT = [[mul(x, y) for y in range(N)] for x in range(N)]
    invT = [inv(x) for x in range(N)]
    darts = [(i, j) for i in range(k) for j in range(k) for _ in range(M[i][j])]
    nd = len(darts)
    while True:
        g = [rng.randrange(N) for _ in range(nd)]
        cost = _vl_cost(g, darts, k, N, mulT, invT)
        T = 2.0
        for step in range(30000):
            if cost == 0:
                darts_full = [(i, k + j, gg) for (i, j), gg in zip(darts, g)]
                yield lib.group_lift(2 * k, darts_full, N, lambda x, y: mulT[x][y])
                return
            if step % 50 == 0:
                yield None
            s = rng.randrange(nd)
            old = g[s]
            new = rng.randrange(N)
            if new == old:
                continue
            g[s] = new
            c = _vl_cost(g, darts, k, N, mulT, invT)
            if c <= cost or rng.random() < math.exp(-(c - cost) / T):
                cost = c
            else:
                g[s] = old
            if T > 0.2:
                T *= 0.9998


def _spawn_vl(d, rng, best_n, moore, mats):
    """Create a random voltage-lift job that could beat best_n, or None."""
    k = rng.choice((2, 3))
    lo = best_n // (2 * k) + 1
    hi = min(lo + 10, moore // (2 * k))
    if lo > hi or not mats[k]:
        return None
    N = rng.randint(lo, hi)
    _, mul, inv = rng.choice(_group_candidates(N, rng))
    M = rng.choice(mats[k])
    return [_vl_job(N, mul, inv, M, rng), 2 * k * N]


def _voltage_phase(d, D, rng, best, deadline, moore):
    """Round-robin search over multi-vertex voltage lifts. Returns the best (n, edges)."""
    mats = {k: _base_matrices(d, k) for k in (2, 3)}
    max_jobs = 4
    jobs = []
    best_n = best[0]
    misses = 0
    while time.monotonic() < deadline:
        while len(jobs) < max_jobs and misses < 50:
            spawned = _spawn_vl(d, rng, best_n, lib.moore_bound(d, D), mats)
            if spawned is None:
                misses += 1
                continue
            jobs.append(spawned)
        if not jobs:
            break
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job[1] <= best_n:
                jobs.remove(job)
                continue
            try:
                res = next(job[0])
            except StopIteration:
                jobs.remove(job)
                continue
            if res is None:
                continue
            jobs.remove(job)
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                jobs = [j for j in jobs if j[1] > best_n]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    moore = lib.moore_bound(d, D)
    best = (base_n, base_e)

    # Phase 1: difference covers (the parent's construction), keeps its wins.
    best = _cayley_phase(d, D, rng, best, start + 0.3 * total, moore)

    # Phase 2: multi-vertex voltage lifts over small non-cyclic groups.
    best = _voltage_phase(d, D, rng, best, deadline, moore)

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return base_n, base_e
