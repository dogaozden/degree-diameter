import itertools
import math
import random
import time

import lib

# Multi-orbit bi-Cayley search (a substantially different family from the parent).
#
# Vertices: A_{i,x} and B_{j,y} for orbits i, j in 0..a-1 and x, y in a group G of order N.
# Each slot t in 0..d-1 has a permutation perms[t] of range(a) and a group element
# gs[t][i]. The dart (slot t, row i) joins A_{i,x} to B_{perms[t][i], x * gs[t][i]}.
# Every A-vertex gets exactly d edges, and every B-vertex gets exactly d edges, since
# each slot is a permutation. Left multiplication by G is an automorphism, so it is
# enough to check eccentricities of the 2a base vertices A_{i,e}, B_{j,e}.
# a = 1 recovers the parent's bi-Cayley search. a >= 2 is the new direction.
# Multi-orbit lifts give graphs of order 2aN with a small group order N.

MAX_GROUPS = 10      # groups tried per (a, N) attempt
ITERS = 4000         # annealing steps per attempt
T_HOT = 6.0          # initial temperature, in unreached-pair units
T_COLD = 0.3         # final temperature
WINDOW_FRAC = 0.8    # first search only orders n >= WINDOW_FRAC * moore bound
BUDGET_START = 0.5   # seconds per (a, N) attempt in the first pass
BUDGET_CAP = 4.0     # cap on per-attempt seconds as passes fail
A_MAX = 6            # max number of orbits per side
SWAP_PROB = 0.35     # probability of a slot-permutation swap move (when a >= 2)
_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# Fallback families (always checked by lib.is_valid before use).
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
# Group helpers.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (k = 1 is cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r, N):
    """Cached (multiplication table, inverse list) for the group Z_m x|_r Z_k of order N."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    if len(_GROUP_CACHE) > 40:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = (T, invs)
    return T, invs


# ----------------------------------------------------------------------------
# Multi-orbit lift search.
# ----------------------------------------------------------------------------

def _row_ok(perms, gs, d, i):
    """Row i has d distinct (target orbit, group element) darts, so no duplicate edges."""
    return len({(perms[t][i], gs[t][i]) for t in range(d)}) == d


def _init(a, d, N, rng):
    """Random slot permutations and group elements, with each row's darts distinct.

    Needs N >= d so that a forbidden set of size < d never covers the whole group.
    """
    perms = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        perms.append(p)
    gs = [[0] * a for _ in range(d)]
    for i in range(a):
        for t in range(d):
            forb = {gs[s][i] for s in range(t) if perms[s][i] == perms[t][i]}
            g = rng.randrange(N)
            while g in forb:
                g = rng.randrange(N)
            gs[t][i] = g
    return perms, gs


def _cost(perms, gs, a, d, N, invs, T, D):
    """Total unreached (source, vertex) pairs over the 2a base sources; 0 iff diameter <= D."""
    aN = a * N
    n = 2 * aN
    listA = [[] for _ in range(a)]
    listB = [[] for _ in range(a)]
    for t in range(d):
        pt = perms[t]
        gt = gs[t]
        inv_t = [0] * a
        for i in range(a):
            j = pt[i]
            listA[i].append((aN + j * N, gt[i]))
            inv_t[j] = i
        for j in range(a):
            i = inv_t[j]
            listB[j].append((i * N, invs[gt[i]]))

    total = 0
    for s in range(2 * a):
        src = s * N if s < a else aN + (s - a) * N
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for joff, g in listA[i]:
                        v = joff + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    row = T[y]
                    for ioff, h in listB[j]:
                        v = ioff + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal(a, d, N, T, invs, D, rng, iters, deadline):
    """Simulated annealing over slot permutations and group elements; returns (perms, gs) or None."""
    perms, gs = _init(a, d, N, rng)
    cur = _cost(perms, gs, a, d, N, invs, T, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        if a >= 2 and rng.random() < SWAP_PROB:
            t = rng.randrange(d)
            i, i2 = rng.sample(range(a), 2)
            pt = perms[t]
            pt[i], pt[i2] = pt[i2], pt[i]
            if _row_ok(perms, gs, d, i) and _row_ok(perms, gs, d, i2):
                v = _cost(perms, gs, a, d, N, invs, T, D)
                if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                    cur = v
                    continue
            pt[i], pt[i2] = pt[i2], pt[i]
        else:
            t = rng.randrange(d)
            i = rng.randrange(a)
            old = gs[t][i]
            new = rng.randrange(N)
            if new == old:
                continue
            gs[t][i] = new
            if _row_ok(perms, gs, d, i):
                v = _cost(perms, gs, a, d, N, invs, T, D)
                if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                    cur = v
                    continue
            gs[t][i] = old
    if cur == 0:
        return perms, gs
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for a orbits per side; return (perms, gs, T) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _group_tables(m, k, r, N)
        st = _anneal(a, d, N, T, invs, D, rng, ITERS, deadline)
        if st is not None:
            return st[0], st[1], T
    return None


def _edges(a, N, d, perms, gs, T):
    """Build the lifted graph: A vertices 0..aN-1, B vertices aN..2aN-1."""
    aN = a * N
    out = []
    for t in range(d):
        for i in range(a):
            j = perms[t][i]
            g = gs[t][i]
            base_b = aN + j * N
            for x in range(N):
                out.append((i * N + x, base_b + T[x][g]))
    return 2 * aN, out


def _candidates(d, Mb, lo):
    """All (a, N) with 2aN in [lo, Mb], a <= A_MAX, N >= d."""
    out = []
    for a in range(1, A_MAX + 1):
        Nmax = Mb // (2 * a)
        Nmin = max(d, -(-lo // (2 * a)))
        for N in range(Nmin, Nmax + 1):
            out.append((a, N))
    return out


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_end = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < search_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Mb = lib.moore_bound(d, D)
    if Mb < 2 * d:
        return best

    # Search orders from the top of the Moore window downward, widening only when
    # a full pass fails. Each success raises best_n and narrows the candidate set.
    floor = max(d + 1, int(WINDOW_FRAC * Mb))
    budget = BUDGET_START

    while time.monotonic() < search_end:
        lo = max(floor, best_n + 1)
        if lo > Mb:
            break
        cands = _candidates(d, Mb, lo)
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for a, N in cands:
            now = time.monotonic()
            if now >= search_end:
                break
            res = _attempt(a, N, d, D, rng, min(search_end, now + budget))
            if res is None:
                continue
            perms, gs, T = res
            n, e = _edges(a, N, d, perms, gs, T)
            consider(n, e)
            success = True
            break
        if not success and time.monotonic() < search_end:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            else:
                floor = max(d + 1, floor - max(1, Mb // 100))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
