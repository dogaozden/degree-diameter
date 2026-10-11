import itertools
import math
import random
import time

import lib

# Search parameters for the voltage-lift search.
MAX_GROUPS = 8          # groups tried per (base size k, group order N) attempt
ITERS = 500             # annealing steps per (group, base) try
T_HOT = 4.0             # initial annealing temperature (unreached-pair units)
T_COLD = 0.4            # final annealing temperature
WINDOW = 24             # look this many vertices above the current floor
KMAX = 4                # base graphs with up to KMAX vertices per side
PERM_MOVE_PROB = 0.25   # chance a move re-randomises one base permutation

_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base multigraphs over groups of order N.
#
# Base: k "A" vertices and k "B" vertices, d perfect matchings (permutations
# perms[t] of range(k)), each dart (A_i -> B_{perms[t][i]}) carrying a group
# voltage volts[t][i]. Lift: A_{i,x} -- B_{j, x*g} for every dart (i, j, g).
# Left multiplication is an automorphism, so only the sources A_{i,0} and
# B_{j,0} need BFS. k = 1 is the bi-Cayley family (arbitrary connection set).
# Vertex indexing: A_{i,x} -> i*N + x, B_{j,y} -> k*N + j*N + y.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(gp):
    """Multiplication table T[x][g] = x*g and inverse table for the group gp (cached)."""
    if gp in _TABLE_CACHE:
        return _TABLE_CACHE[gp]
    m, k, r = gp
    N, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    if len(_TABLE_CACHE) > 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[gp] = (T, invs)
    return T, invs


def _unreached(k, N, T, invs, perms, volts, d, D):
    """Count (source, vertex) pairs not within distance D over all 2k layer sources."""
    kN = k * N
    V = 2 * kN
    fwd = [[] for _ in range(k)]
    rev = [[] for _ in range(k)]
    for t in range(d):
        for i in range(k):
            j = perms[t][i]
            g = volts[t][i]
            fwd[i].append((j, g))
            rev[j].append((i, invs[g]))
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in fwd[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, gi in rev[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over base permutations and voltages to zero unreached pairs."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    volts = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cur = _unreached(k, N, T, invs, perms, volts, d, D)
    for it in range(iters):
        if cur == 0:
            return perms, volts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(d)
        if k > 1 and rng.random() < PERM_MOVE_PROB:
            p2 = [row[:] for row in perms]
            p2[t] = rng.sample(range(k), k)
            v2 = volts
        else:
            p2 = perms
            v2 = [row[:] for row in volts]
            i = rng.randrange(k)
            g = rng.randrange(N)
            if g == v2[t][i]:
                continue
            v2[t][i] = g
        v = _unreached(k, N, T, invs, p2, v2, d, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            perms, volts, cur = p2, v2, v
    if cur == 0:
        return perms, volts
    return None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for base size k until one yields diameter <= D, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for gp in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        T, invs = _tables(gp)
        res = _anneal(k, N, T, invs, d, D, rng, ITERS, deadline)
        if res is not None:
            perms, volts = res
            return T, perms, volts
    return None


def _edges(k, N, T, perms, volts, d):
    """Materialise the lift as (n, sorted edge list) with A indices below B indices."""
    kN = k * N
    E = set()
    for t in range(d):
        for i in range(k):
            j = perms[t][i]
            g = volts[t][i]
            for x in range(N):
                E.add((i * N + x, kN + j * N + T[x][g]))
    return 2 * kN, sorted(E)


def _search(d, D, rng, deadline, consider, get_best_n):
    """Ascending-window search over (k, N) voltage lifts above the current best."""
    cap = lib._moore_bound(d, D)
    floor_n = int(0.45 * cap)
    use_floor = True
    budget = 0.3
    banned = set()
    while time.monotonic() < deadline:
        best_n = get_best_n()
        lo = max(best_n, floor_n if use_floor else 0)
        cands = []
        for h in range(lo // 2 + 1, (lo + WINDOW) // 2 + 1):
            n = 2 * h
            if n > cap:
                break
            for k in range(1, KMAX + 1):
                if h % k == 0 and h // k >= 2:
                    key = (n, k, h // k)
                    if key not in banned:
                        cands.append(key)
        if not cands:
            if use_floor and floor_n > best_n:
                use_floor = False
                continue
            break
        cands.sort(key=lambda c: (c[0], rng.random()))
        success = False
        for n, k, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, perms, volts = res
            nn, edges = _edges(k, N, T, perms, volts, d)
            before = get_best_n()
            consider(nn, edges)
            if get_best_n() > before:
                success = True
                break
            banned.add((n, k, N))
        if not success:
            budget *= 2
            if use_floor and budget >= 2.0 and floor_n > best_n:
                use_floor = False
                budget = 0.3


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def get_best_n():
        return best_n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best

    try:
        _search(d, D, rng, deadline, consider, get_best_n)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
