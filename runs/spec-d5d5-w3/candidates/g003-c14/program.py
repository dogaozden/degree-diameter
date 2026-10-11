import math
import random
import time

import lib

# Known record orders for the scored targets. Phase 1 tries to reproduce the
# record; phase 2 climbs above it.
RECORD = {(5, 5): 336, (3, 3): 14}

MAX_GROUPS = 25    # semidirect groups tried per (k, N) candidate
RESTARTS = 3       # fresh random base graphs and voltages per group
ITERS = 700        # annealing steps per restart
WINDOW = 10        # phase 2 looks this many orders above the current best
START_BUDGET = 1.0 # seconds spent per order in the first phase-2 pass
GROWTH = 1.5       # budget multiplier between phase-2 passes

_group_cache = {}


# ----------------------------------------------------------------------------
# Idea: multi-orbit voltage lifts over semidirect groups.
#
# A bi-Cayley graph (k = 1) has one orbit per side. Here the base graph has k
# A-vertices and k B-vertices, and the base is d-regular: it is the union of d
# random permutations of range(k), so every base vertex has d darts. Each dart
# (i, j) carries a voltage g in a group G of order N. The lift has vertices
# A(i,x), B(j,y) for x, y in G, with A(i,x) ~ B(j, x*g). Every vertex has
# degree d and the graph is bipartite. Parallel darts between the same (i, j)
# get distinct voltages, so there are no duplicate edges.
#
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from A(i,0) and B(j,0) for the 2k base representatives. Annealing moves
# single voltages to reduce the number of pairs at distance > D. Orders
# 2kN with k = 2, 3 are new relative to the bi-Cayley search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in _group_cache:
        return _group_cache[N]
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    _group_cache[N] = out
    return out


def _table(m, kk, r):
    """Multiplication table T[x][g] = x*g and the inverse list for the group."""
    N = m * kk
    _, mul, inv = lib.semidirect_group(m, kk, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _base(k, d, rng):
    """Darts (i, j) of a d-regular bipartite base multigraph on k + k vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, perm[i]))
    return darts


def _init_vol(darts, N, rng):
    """Random voltages, distinct among darts that share the same (i, j)."""
    vol = []
    used = {}
    for pair in darts:
        forb = used.setdefault(pair, [])
        while True:
            g = rng.randrange(N)
            if g not in forb:
                break
        forb.append(g)
        vol.append(g)
    return vol


def _cost(k, N, D, T, invs, darts, vol):
    """Number of (source, vertex) pairs at distance > D over the 2k base representatives."""
    kN = k * N
    V = 2 * kN
    out_e = [[] for _ in range(k)]
    in_e = [[] for _ in range(k)]
    for (i, j), g in zip(darts, vol):
        out_e[i].append((j, g))
        in_e[j].append((i, invs[g]))
    total = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
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
                    for j, g in out_e[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in in_e[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, d, D, T, invs, darts, rng, iters, deadline):
    """Anneal the voltages until the cost is zero; return the voltages or None."""
    vol = _init_vol(darts, N, rng)
    cur = _cost(k, N, D, T, invs, darts, vol)
    E = len(darts)
    same = [[f for f in range(E) if f != e and darts[f] == darts[e]] for e in range(E)]
    for it in range(iters):
        if cur == 0:
            return vol
        if time.monotonic() > deadline:
            break
        e = rng.randrange(E)
        forb = {vol[f] for f in same[e]}
        c = rng.randrange(N)
        if c in forb or c == vol[e]:
            continue
        old = vol[e]
        vol[e] = c
        v = _cost(k, N, D, T, invs, darts, vol)
        temp = max(0.25, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[e] = old
    return vol if cur == 0 else None


def _search(k, N, d, D, rng, deadline):
    """Search a (k, N) candidate over several groups; return (n, edges) or None."""
    groups = list(_groups(N))
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _table(m, kk, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            darts = _base(k, d, rng)
            vol = _anneal(k, N, d, D, T, invs, darts, rng, ITERS, deadline)
            if vol is not None:
                kN = k * N
                edges = [(i * N + x, kN + j * N + T[x][g])
                         for (i, j), g in zip(darts, vol) for x in range(N)]
                return 2 * kN, edges
    return None


def _try_order(V, plan, d, D, rng, deadline):
    """Try to realise order V; plan is a list of (k, seconds) for the orbit counts k."""
    for k, budget in plan:
        if V % (2 * k):
            continue
        N = V // (2 * k)
        if N < max(d, 2):
            continue
        now = time.monotonic()
        if now >= deadline:
            return None
        res = _search(k, N, d, D, rng, min(deadline, now + budget))
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact or known constructions first; these return quickly.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if lib.is_valid(best[0], best[1], d, D):
            return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except ValueError:
            pass
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    Vmoore = lib._moore_bound(d, D)
    target = RECORD.get((d, D))

    # Phase 1: reproduce the known record order with the new multi-orbit lifts first.
    if target is not None and target <= Vmoore and time.monotonic() < deadline:
        plan = [(2, 3.5), (1, 3.5), (3, 2.0), (4, 1.0)]
        res = _try_order(target, plan, d, D, rng, deadline)
        if res is not None:
            consider(*res)

    # Phase 2: climb above the current best order, with growing budgets per pass.
    budget = START_BUDGET
    while time.monotonic() < deadline:
        v = best[0] + 1
        top = min(Vmoore, best[0] + WINDOW)
        while v <= top and time.monotonic() < deadline:
            ks = [k for k in (2, 1, 3, 4) if v % (2 * k) == 0 and v // (2 * k) >= max(d, 2)]
            if ks:
                per = budget / len(ks)
                plan = [(k, per) for k in ks]
                res = _try_order(v, plan, d, D, rng, deadline)
                if res is not None:
                    consider(*res)
            v += 1
            top = min(Vmoore, best[0] + WINDOW)
        budget *= GROWTH

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
