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
# Single-base lift: two base vertices a, b with darts (a, b, s) for s in S give
# a bipartite graph on G x {0,1} with a_x ~ b_{x s}. Diameter <= 3 exactly when
# S S^{-1} = G (a difference cover of size d).
#
# NEW: multi-base lifts. Take k A-vertices and k B-vertices, and let the base
# multigraph be the union of d random permutations (so it is d-regular). Give
# each dart a voltage in a group G of order N. The lift has 2kN vertices, is
# bipartite, and has max degree d. Voltages are annealed to minimise the number
# of vertex pairs at distance > 3. Because left multiplication by G is an
# automorphism of the lift, only the k A-base-vertices and k B-base-vertices at
# the identity need BFS sources.

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


def _lift_cost(k, N, mt, darts_ij, volt, n, D):
    """Number of (source, vertex) pairs at distance > D, over the 2k base sources at the identity."""
    adj = [[] for _ in range(n)]
    for (i, j), g in zip(darts_ij, volt):
        ai = i * N
        bj = (k + j) * N
        for x in range(N):
            a = ai + x
            b = bj + mt[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for s in range(2 * k):
        src = s * N
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - cnt
    return total


def _lift_anneal(k, N, mul, d, D, rng):
    """Generator: anneal voltages of a random d-regular k+k base multigraph over a group of order N.

    Yields None periodically and yields (darts_ij, voltages) once cost reaches 0.
    """
    mt = [[mul(x, g) for g in range(N)] for x in range(N)]
    n = 2 * k * N
    while True:
        perms = [rng.sample(range(k), k) for _ in range(d)]
        darts_ij = [(i, perms[j][i]) for j in range(d) for i in range(k)]
        volt = [rng.randrange(N) for _ in darts_ij]
        cost = _lift_cost(k, N, mt, darts_ij, volt, n, D)
        T = 1.0
        for step in range(3000):
            if cost == 0:
                break
            if step % 25 == 0:
                yield None
            t = rng.randrange(len(volt))
            old = volt[t]
            volt[t] = rng.randrange(N)
            c2 = _lift_cost(k, N, mt, darts_ij, volt, n, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                volt[t] = old
            T = max(0.2, T * 0.999)
        if cost == 0:
            yield (darts_ij, list(volt))
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

    moore = lib.moore_bound(d, D)
    best_n = base_n
    best = (base_n, base_e)

    # Each active entry: (kind, capacity, k, N, mul, generator).
    active = []

    # 1) Single-base difference-cover lifts (k = 1), as before.
    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
            gen = _anneal(N, mul, inv, d, rng)
            active.append(("diff", 2 * N, 1, N, mul, gen))

    # 2) NEW: multi-base lifts with k = 2..5 base vertices per side.
    for k in (2, 3, 4, 5):
        lo_N = best_n // (2 * k) + 1
        hi_N = moore // (2 * k)
        for N in list(range(lo_N, hi_N + 1))[:6]:
            for _order, mul, inv in _group_list(N, rng)[:2]:
                gen = _lift_anneal(k, N, mul, d, D, rng)
                active.append(("lift", 2 * k * N, k, N, mul, gen))

    active = [e for e in active if e[1] > best_n]

    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            kind, cap, k, N, mul, gen = entry
            if cap <= best_n:
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
            if kind == "diff":
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            else:
                darts_ij, volt = res
                darts = [(i, k + j, g) for (i, j), g in zip(darts_ij, volt)]
                n, edges = lib.group_lift(2 * k, darts, N, mul)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                active = [e for e in active if e[1] > best_n]
        active = [e for e in active if e[1] > best_n]

    return best

