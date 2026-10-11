import itertools
import math
import random
import time

import lib

ITERS = 800                   # annealing steps per (group, base-voltage) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
MAX_GROUPS = 10               # groups tried per (t, N) attempt
BUDGET_START = 1.5            # seconds per attempt, first time
BUDGET_CAP = 8.0              # cap on per-attempt seconds
GROUP_MOVE_PROB = 0.5         # chance a voltage move multiplies two current voltages
PERM_MOVE_PROB = 0.5          # chance a move re-draws a base permutation (t > 1)
N_UP_PROB = 0.35              # chance to move to the next order after a failed attempt
T_CHOICES = (2, 3, 1, 4, 5, 6)  # base sizes per side, tried round-robin


# ----------------------------------------------------------------------------
# Baseline families (fast; every result is checked with lib.is_valid).
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
# Generalized voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: t vertices A_0..A_{t-1} and t vertices B_0..B_{t-1}, with d darts
# (perm_k, g_k), k = 0..d-1. Dart k joins A_{i,x} to B_{perm_k[i], x*g_k} for all x.
# WLOG perm_0 = identity and g_0 = identity. The lift has 2*t*N vertices and is
# d-regular. Left multiplication by G is an automorphism that is transitive on each
# fibre, so the diameter is decided by BFS from A_{i,e} and B_{j,e} only.
# t = 1 is exactly the bi-Cayley search over one connection set.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    """Return (N, T) with T[x][g] = x*g for the group Z_m x|_r Z_k (identity coded 0)."""
    key = (m, k, r)
    if key not in _GROUP_CACHE:
        if len(_GROUP_CACHE) > 40:
            _GROUP_CACHE.clear()
        N, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        _GROUP_CACHE[key] = (N, T)
    return _GROUP_CACHE[key]


def _darts_ok(t, perms, gs):
    """True if no two darts give the same (i, j, g) triple, i.e. no duplicate edges."""
    seen = set()
    for sg, g in zip(perms, gs):
        for i in range(t):
            tr = (i, sg[i], g)
            if tr in seen:
                return False
            seen.add(tr)
    return True


def _cost(t, N, T, perms, gs, D):
    """Number of (source, vertex) pairs at distance > D, over the 2t fibre representatives."""
    base = t * N
    V = 2 * base
    adj = [[] for _ in range(V)]
    for sg, g in zip(perms, gs):
        for i in range(t):
            ai = i * N
            bj = base + sg[i] * N
            for x in range(N):
                a = ai + x
                b = bj + T[x][g]
                adj[a].append(b)
                adj[b].append(a)
    total = 0
    sources = [i * N for i in range(t)] + [base + j * N for j in range(t)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(t, N, T, d, D, rng, perms_all, iters, deadline):
    """Simulated annealing over the base permutations and voltages to reach zero unreached pairs."""
    ident = tuple(range(t))
    perms = gs = None
    for _ in range(50):
        if t > 1:
            perms = [ident] + [rng.choice(perms_all) for _ in range(d - 1)]
        else:
            perms = [ident] * d
        gs = [0] + [rng.randrange(1, N) for _ in range(d - 1)]
        if _darts_ok(t, perms, gs):
            break
    else:
        return None

    cur = _cost(t, N, T, perms, gs, D)
    for it in range(iters):
        if cur == 0:
            return perms, gs
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(1, d)
        if t > 1 and rng.random() < PERM_MOVE_PROB:
            perms2 = perms[:]
            perms2[k] = rng.choice(perms_all)
            gs2 = gs
        else:
            perms2 = perms
            if rng.random() < GROUP_MOVE_PROB:
                a = gs[rng.randrange(d)]
                g = gs[rng.randrange(d)]
                c = T[a][g]
            else:
                c = rng.randrange(1, N)
            gs2 = gs[:]
            gs2[k] = c
        if not _darts_ok(t, perms2, gs2):
            continue
        v = _cost(t, N, T, perms2, gs2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            perms, gs, cur = perms2, gs2, v
    if cur == 0:
        return perms, gs
    return None


def _attempt(t, N, d, D, rng, perms_all, deadline):
    """Try groups of order N for base size t until one yields a valid lift, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, T = _group_table(m, k, r)
        res = _anneal(t, N, T, d, D, rng, perms_all, ITERS, deadline)
        if res is not None:
            perms, gs = res
            return T, perms, gs
    return None


def _lift_graph(t, N, T, perms, gs):
    """Edge list and vertex count of the lift: A block = 0..tN-1, B block = tN..2tN-1."""
    base = t * N
    edges = set()
    for sg, g in zip(perms, gs):
        for i in range(t):
            j = sg[i]
            for x in range(N):
                edges.add((i * N + x, base + j * N + T[x][g]))
    return 2 * base, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

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
        return best

    total_max = lib._moore_bound(d, D)
    perms_cache = {t: list(itertools.permutations(range(t))) for t in T_CHOICES}
    Ncur = {}
    budget = {t: BUDGET_START for t in T_CHOICES}

    while time.monotonic() < deadline:
        for t in T_CHOICES:
            now = time.monotonic()
            if now >= deadline:
                break
            # Smallest order whose lift would beat the current best.
            n_min = best_n // (2 * t) + 1
            N = max(Ncur.get(t, n_min), n_min)
            Ncur[t] = N
            if 2 * t * N > total_max or N < d + 1:
                continue
            att_deadline = min(deadline, now + budget[t])
            res = _attempt(t, N, d, D, rng, perms_cache[t], att_deadline)
            if res is None:
                budget[t] = min(BUDGET_CAP, budget[t] * 1.3)
                if rng.random() < N_UP_PROB:
                    Ncur[t] = N + 1
                continue
            T, perms, gs = res
            n, e = _lift_graph(t, N, T, perms, gs)
            consider(n, e)
            budget[t] = BUDGET_START

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
