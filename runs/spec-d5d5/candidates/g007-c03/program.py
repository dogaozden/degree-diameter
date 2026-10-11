import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (k, N) attempt
ITERS = 600                   # annealing steps per attempt


# ----------------------------------------------------------------------------
# Baseline family: PG(2, q) incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New idea: k-orbit bi-regular voltage lifts over semidirect products.
#
# Vertices: A_{i,x} (i < k, x in G) and B_{j,y} (j < k, y in G), |G| = N.
# Each A-orbit i has d darts (i, j, g); the dart joins A_{i,x} to B_{j, x*g}.
# The targets j are a balanced multiset, so every B-orbit also gets exactly
# d darts, and the lift is d-regular and bipartite with 2kN vertices.
#
# Left multiplication by G is an automorphism, so the eccentricity of every
# vertex equals that of its orbit representative. The 2k representatives
# A_{i,e} and B_{j,e} therefore decide the diameter. The search anneals the
# voltages to zero out the count of (source, vertex) pairs at distance > D.
# k = 1 recovers the single-orbit bi-Cayley search.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _make_darts(k, d, N, rng):
    """Random darts [i, j, g]: A-orbit i gets d darts; every B-orbit j receives exactly d."""
    targets = [j for j in range(k) for _ in range(d)]
    rng.shuffle(targets)
    darts = []
    idx = 0
    for i in range(k):
        for _ in range(d):
            darts.append([i, targets[idx], rng.randrange(N)])
            idx += 1
    return darts


def _unreached(k, N, T, invs, from_list, into_list, D):
    """Total count of (source, vertex) pairs not within distance D over the 2k orbit representatives."""
    base_b = k * N
    V = 2 * k * N
    sources = [i * N for i in range(k)] + [base_b + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base_b:
                    i, x = divmod(u, N)
                    row = T[x]
                    for dart in from_list[i]:
                        v = base_b + dart[1] * N + row[dart[2]]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base_b, N)
                    row = T[y]
                    for dart in into_list[j]:
                        v = dart[0] * N + row[invs[dart[2]]]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, T, invs, darts, from_list, into_list, D, rng, iters, deadline):
    """Anneal dart voltages until the diameter is at most D. Returns True on success."""
    cur = _unreached(k, N, T, invs, from_list, into_list, D)
    for it in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            break
        temp = max(0.5, 4.0 * (1.0 - it / iters))
        dart = darts[rng.randrange(len(darts))]
        old = dart[2]
        new = rng.randrange(N)
        if new == old:
            continue
        dart[2] = new
        v = _unreached(k, N, T, invs, from_list, into_list, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            dart[2] = old
    return cur == 0


def _attempt(k, N, d, D, rng, deadline):
    """Try several groups of order N with k orbits. Returns (T, darts) on success, else None."""
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            break
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _make_darts(k, d, N, rng)
        from_list = [[] for _ in range(k)]
        into_list = [[] for _ in range(k)]
        for dt in darts:
            from_list[dt[0]].append(dt)
            into_list[dt[1]].append(dt)
        if _anneal(k, N, T, invs, darts, from_list, into_list, D, rng, ITERS, deadline):
            return T, darts
    return None


def _edges(k, N, T, darts):
    """Expand darts into the explicit edge list of the 2kN-vertex lift."""
    base_b = k * N
    es = set()
    for i, j, g in darts:
        for x in range(N):
            es.add((i * N + x, base_b + j * N + T[x][g]))
    return 2 * k * N, sorted(es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    if d < 2 or D < 2:
        return best

    mb = lib._moore_bound(d, D)
    half = mb // 2          # 2kN <= mb  =>  kN <= half
    budget = 2.0

    while time.monotonic() < deadline:
        found = False
        ks = [1, 2, 3, 4]
        rng.shuffle(ks)
        for k in ks:
            now = time.monotonic()
            if now >= deadline:
                break
            Nmin = max(1, best[0] // (2 * k) + 1)
            Nmax = half // k
            if Nmin > Nmax:
                continue
            N = min(Nmax, Nmin + rng.randrange(3))
            att = min(deadline, now + budget)
            res = _attempt(k, N, d, D, rng, att)
            if res is None:
                continue
            T, darts = res
            n, e = _edges(k, N, T, darts)
            consider(n, e)
            found = True
            break
        if not found:
            budget = min(budget * 1.5, 15.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
