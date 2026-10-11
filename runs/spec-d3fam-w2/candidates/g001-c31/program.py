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


# ------------------------------------------------ Cayley-type bipartite lifts (2 base vertices)

def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
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


def _cayley_search(d, rng, deadline, floor_n):
    """Parent's difference-cover search. Returns (n, edges) with n > floor_n, or None."""
    lo = floor_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])

    best = None
    best_N = lo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if job[0] <= best_N:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search(N, R, d, rng, 1200, deadline)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > floor_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                break
        jobs = [j for j in jobs if j[0] > best_N]
    return best


# ------------------------------------------ NEW: 2+2 base lifts (two A-, two B-vertices)
#
# Base graph: A0, A1 (one side), B0, B1 (other side). Block multiplicities
#     c = [[a, d-a], [d-a, a]]
# force every base vertex to have degree d. Voltages v in G give the lift
#     A_i x ~ B_j (x v),
# which is bipartite, d-regular, has 4|G| vertices, and is G-invariant under
# left multiplication. So the diameter is <= 3 iff the balls of radius 3 around
# the four base vertices A_i e, B_j e cover everything. Cost = total number of
# uncovered (source, vertex) pairs, minimised by simulated annealing over the
# voltages. This is a richer search space than the 2-vertex difference cover,
# and its order 4|G| can reach the Moore-type bound 2(1 + d(d-1)).

def _tables(N, mul, inv):
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(y) for y in range(N)]
    return M, I


def _lift_cost(N, M, I, k, bl, vs):
    """Uncovered (source, vertex) pairs at distance > 3 for the 2k+2k-vertex lift."""
    nbA = [[] for _ in range(k)]
    nbB = [[] for _ in range(k)]
    for (i, j), v in zip(bl, vs):
        nbA[i].append((j, v))
        nbB[j].append((i, I[v]))
    kN = k * N
    total = 2 * kN
    cost = 0
    sources = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    for src in sources:
        seen = {src}
        frontier = [src]
        for _ in range(3):
            nxt = []
            for c in frontier:
                if c < kN:
                    i, x = divmod(c, N)
                    row = M[x]
                    for j, v in nbA[i]:
                        t = kN + j * N + row[v]
                        if t not in seen:
                            seen.add(t)
                            nxt.append(t)
                else:
                    j, y = divmod(c - kN, N)
                    row = M[y]
                    for i, iv in nbB[j]:
                        t = i * N + row[iv]
                        if t not in seen:
                            seen.add(t)
                            nxt.append(t)
            frontier = nxt
            if not frontier:
                break
        cost += total - len(seen)
    return cost


def _init_volts(N, bl, rng):
    """Random voltages with distinct values inside each block (so no parallel edges)."""
    vs = [0] * len(bl)
    for b in set(bl):
        idx = [t for t, x in enumerate(bl) if x == b]
        for t, v in zip(idx, rng.sample(range(N), len(idx))):
            vs[t] = v
    return vs


def _anneal(job, rng, steps, deadline, k):
    N, M, I, bl, blk, vs = job['N'], job['M'], job['I'], job['bl'], job['blk'], job['vs']
    cur = job['cur']
    T = job['T']
    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        t = rng.randrange(len(vs))
        used = {vs[u] for u in blk[bl[t]] if u != t}
        new = rng.randrange(N)
        while new in used:
            new = rng.randrange(N)
        old = vs[t]
        vs[t] = new
        c = _lift_cost(N, M, I, k, bl, vs)
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            cur = c
        else:
            vs[t] = old
    job['cur'] = cur
    job['T'] = max(0.4, T * 0.98)


def _lift_search(d, D, rng, deadline, floor_n):
    """Search 2+2 base lifts. Returns (n, edges) with n > floor_n, or None."""
    k = 2
    Nhi = (1 + d * (d - 1)) // 2          # 4N <= 2(1 + d(d-1))
    Nlo = floor_n // (2 * k) + 1          # 4N > floor_n
    if Nlo > Nhi:
        return None

    jobs = []
    for N in range(Nhi, Nlo - 1, -1):
        for _o, mul, inv in _group_list(N, rng)[:4]:
            M, I = _tables(N, mul, inv)
            for a in range(1, d // 2 + 1):
                bl = ([(0, 0)] * a + [(0, 1)] * (d - a)
                      + [(1, 0)] * (d - a) + [(1, 1)] * a)
                blk = {}
                for t, b in enumerate(bl):
                    blk.setdefault(b, []).append(t)
                vs = _init_volts(N, bl, rng)
                job = {
                    'N': N, 'M': M, 'I': I, 'mul': mul, 'bl': bl, 'blk': blk,
                    'vs': vs, 'T': 2.0,
                    'cur': _lift_cost(N, M, I, k, bl, vs),
                }
                jobs.append(job)

    best = None
    best_N = Nlo - 1
    while jobs and time.monotonic() < deadline:
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            if job['N'] <= best_N:
                continue
            _anneal(job, rng, 60, deadline, k)
            if job['cur'] == 0:
                darts = [(i, k + j, v) for (i, j), v in zip(job['bl'], job['vs'])]
                n, edges = lib.group_lift(2 * k, darts, job['N'], job['mul'])
                if n > floor_n and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                    best_N = job['N']
                    break
                job['N'] = -1  # should not happen; drop this job
        jobs = [j for j in jobs if j['N'] > best_N]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime with d-1 not a prime power is searched.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best_n = base_n

    # Phase 1 (short): Cayley-type difference-cover search from the parent.
    span = deadline - start
    cay_deadline = start + 0.15 * span
    try:
        cay = _cayley_search(d, rng, cay_deadline, best_n)
        if cay is not None and cay[0] > best_n and lib.is_valid(cay[0], cay[1], d, D):
            best = cay
            best_n = cay[0]
    except Exception:
        pass

    # Phase 2: 2+2 base lifts with annealed voltages.
    try:
        lf = _lift_search(d, D, rng, deadline, best_n)
        if lf is not None and lf[0] > best_n and lib.is_valid(lf[0], lf[1], d, D):
            best = lf
    except Exception:
        pass

    return best
