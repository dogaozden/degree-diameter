import math
import random
import time

import lib

T_HOT = 1.5          # initial annealing temperature (unreached-pair units)
T_COLD = 0.15        # final annealing temperature
ITERS = 500          # annealing steps per (group, pattern) try
GROUPS_PER_TRY = 6   # groups tried for each (base size, order) attempt
P_CHOICES = [1, 2, 2, 3, 3, 4]   # number of A-orbits (= B-orbits) in the base


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Base graph: p "A" vertices and p "B" vertices, joined by darts. A d-regular
# base is given by a p x p multiplicity matrix C with all row and column sums d
# (a sum of d random permutation matrices). Each block (i, j) carries C[i][j]
# distinct voltages g in G. Lift vertices:
#     A_{i,x} = i*N + x,      B_{j,y} = p*N + j*N + y,      x, y in G.
# Edges: A_{i,x} -- B_{j, x*g} for every block (i, j) and voltage g in it.
#
# Left multiplication by any h in G is an automorphism, so the orbit of each
# base vertex is all of its lift copies. Eccentricities from the 2p
# identity-coset representatives decide the diameter.
# With p = 1 this is the usual bi-Cayley graph; p >= 2 gives a richer family.
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


def _pattern(p, d, rng):
    """Random d-regular p x p multiplicity matrix (sum of d random permutations)."""
    C = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            C[i][perm[i]] += 1
    return C


def _cost(p, N, T, vol, D):
    """Total number of (source, vertex) pairs at distance > D, over the 2p representatives."""
    tot = 2 * p * N
    adj = [[] for _ in range(tot)]
    for i in range(p):
        for j in range(p):
            base_b = p * N + j * N
            for g in vol[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    sources = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    unreached = 0
    for s in sources:
        seen = bytearray(tot)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        unreached += tot - cnt
    return unreached


def _anneal(p, N, T, C, D, rng, deadline):
    """Anneal voltages so that every source reaches everything within D.

    Returns the voltage table vol[i][j] (a list of C[i][j] distinct group elements)
    or None if no zero-cost configuration was found.
    """
    blocks = [(i, j) for i in range(p) for j in range(p) if C[i][j] > 0]
    vol = [[rng.sample(range(N), C[i][j]) if C[i][j] else [] for j in range(p)]
           for i in range(p)]
    cur = _cost(p, N, T, vol, D)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i, j = rng.choice(blocks)
        k = rng.randrange(C[i][j])
        g = rng.randrange(N)
        if g in vol[i][j]:
            continue
        old = vol[i][j][k]
        vol[i][j][k] = g
        v = _cost(p, N, T, vol, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            vol[i][j][k] = old
    return vol if cur == 0 else None


def _edges(p, N, T, vol):
    """Explicit edge list of the lift. Distinct voltages in a block give distinct edges."""
    edges = []
    for i in range(p):
        for j in range(p):
            for g in vol[i][j]:
                for x in range(N):
                    edges.append((i * N + x, p * N + j * N + T[x][g]))
    return 2 * p * N, edges


def _search(d, D, rng, deadline, consider, moore):
    """Random walk over (base size p, order N): climb on success, back off after repeated failure."""
    N_try = {}
    fails = {}
    while time.monotonic() < deadline:
        p = rng.choice(P_CHOICES)
        cap = moore // (2 * p)
        if p not in N_try:
            N_try[p] = max(d + 1, int(0.45 * cap))
            fails[p] = 0
        N = min(N_try[p], cap)
        if N < d + 1:
            N_try[p] = d + 1
            continue
        groups = _groups(N)
        rng.shuffle(groups)
        C = _pattern(p, d, rng)
        ok = False
        for m, k, r in groups[:GROUPS_PER_TRY]:
            if time.monotonic() > deadline:
                break
            _, mul, _ = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            vol = _anneal(p, N, T, C, D, rng, deadline)
            if vol is not None:
                n, e = _edges(p, N, T, vol)
                if consider(n, e):
                    ok = True
                break
        if ok:
            N_try[p] = N + 1
            fails[p] = 0
        else:
            fails[p] += 1
            if fails[p] >= 2:
                N_try[p] = max(d + 1, N - 1)
                fails[p] = 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2 and d >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2 and time.monotonic() < deadline:
        moore = lib._moore_bound(d, D)
        _search(d, D, rng, deadline, consider, moore)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
