import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables
# ----------------------------------------------------------------------------

MAX_GROUPS = 12          # groups tried per order N in one bi-Cayley attempt
ITERS = 800              # annealing steps per (group, connection set) try
MULTI_ITERS = 800        # annealing steps for multi-base lifts
T_HOT = 1.5              # bi-Cayley annealing start temperature
T_COLD = 0.15            # bi-Cayley annealing end temperature
GROUP_MOVE_PROB = 0.5    # chance a bi-Cayley move proposes a product of two set elements
BUDGET_START = 1.0       # seconds per search attempt at first
BUDGET_CAP = 6.0         # cap on per-attempt seconds
BICAYLEY_PROB_D4 = 0.85  # share of bi-Cayley attempts when D >= 4
BICAYLEY_PROB_D3 = 0.6   # share of bi-Cayley attempts when D == 3
_BIG = 10 ** 9
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k (order N, graph has 2N
# vertices). Vertices A_x, B_y (x, y in G); A_x ~ B_{x g} for g in S, |S| = d,
# 0 in S. Left translation is an automorphism, so the eccentricities of A_0 and
# B_0 decide the diameter.
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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal_bicayley(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs.

    Moves either replace one element uniformly at random, or replace it with a
    group product of two current elements (keeps candidates structured).
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        if rng.random() < GROUP_MOVE_PROB:
            a = S[rng.randrange(d)]
            g = S[rng.randrange(d)]
            c = T[a][g]
        else:
            c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt_bicayley(N, d, D, rng, deadline):
    """Try random groups of order N until one yields a valid connection set, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, _, T, invs = _tables(m, k, r)
        S = _anneal_bicayley(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# k left and k right base vertices, d layers; each layer is a perfect matching
# between left and right base vertices with a group voltage per dart.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost_multi(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges_multi(k, G, darts, perms):
    """Edge list of the multi-base lift described by darts and perms."""
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_multi(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer matchings."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost_multi(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost_multi(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_multi(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_multi(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # K_{d,d}: diameter 2, meets the Moore bound for D = 2.
    consider(*lib.haar_graph(d, range(d)))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    if D == 3:
        # Record construction when d - 1 is a prime power.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record when d - 2 is a prime power (>= 3).
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    else:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best[0] >= moore or d < 2:
        return best

    Nmax = moore // 2
    if Nmax < d + 1:
        return best

    # Bi-Cayley window: orders near the top of the Moore range first, then widen.
    top = min(Nmax, Nmax // 2 + 6)
    floor = max(d + 1, int(0.95 * top))
    bicayley_prob = BICAYLEY_PROB_D4 if D >= 4 else BICAYLEY_PROB_D3
    att_budget = BUDGET_START
    fails = 0

    try:
        while time.monotonic() < deadline:
            n_best = best[0]
            if n_best >= moore:
                break
            att_deadline = min(deadline, time.monotonic() + att_budget)
            improved = False

            if rng.random() < bicayley_prob:
                lo = max(floor, n_best // 2 + 1)
                if lo > Nmax:
                    break
                hi = min(Nmax, max(lo, top))
                N = rng.randint(lo, hi)
                res = _attempt_bicayley(N, d, D, rng, att_deadline)
                if res is not None:
                    T, S = res
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
                    improved = best[0] > n_best
            else:
                k = rng.choice((2, 3))
                gmax = moore // (2 * k)
                lo = n_best // (2 * k) + 1
                if lo <= gmax:
                    G = rng.randint(lo, min(gmax, lo + max(2, lo // 10)))
                    gs = _groups(G)
                    if gs:
                        m, k2, r = rng.choice(gs)
                        order, mul, _ = lib.semidirect_group(m, k2, r)
                        res = _anneal_multi(d, D, k, order, mul, rng, att_deadline, MULTI_ITERS)
                        if res is not None:
                            consider(res[0], res[1])
                            improved = best[0] > n_best

            if improved:
                fails = 0
                continue

            fails += 1
            if fails % 4 == 0:
                att_budget = min(BUDGET_CAP, att_budget * 1.3)
                floor = max(d + 1, floor - 2)
                top = min(Nmax, top + 3)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
