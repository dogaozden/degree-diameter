import math
import random
import time

import lib

ITERS = 500            # annealing steps per (group, base structure) try
T_HOT = 1.2            # initial temperature (unreached-pair units)
T_COLD = 0.1           # final temperature
MAX_A = 4              # largest base-fiber count per side tried (a x a base multigraph)
WINDOW0 = 12           # number of smallest-order candidates attempted per pass
WINDOW_MAX = 80        # cap on candidate window growth after failed passes


# ----------------------------------------------------------------------------
# Baseline families (kept for small / calibration cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-fiber group lifts over a semidirect product G = Z_m x| Z_k, |G| = N.
#
# Vertex sets: A_{i,x} (i < a, x in G) and B_{j,y} (j < a, y in G).
# A "dart" (i, j, g) joins A_{i,x} to B_{j, x*g} for every x in G.
# Each A fiber gets d darts and each B fiber gets d darts, so the lift is
# d-regular and simple (distinct darts at a fiber use distinct targets).
#
# Left multiplication by y in G is an automorphism of the lift, so each fiber
# is a single orbit. The diameter is therefore certified by BFS from one
# representative per fiber (A_{i,e} and B_{j,e}), which is 2a BFS runs.
# The old bi-Cayley search is the special case a = 1.
# ----------------------------------------------------------------------------

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


def _adjacency(a, N, darts, T):
    """Adjacency lists of the lift described by the darts."""
    n = 2 * a * N
    aN = a * N
    adj = [[] for _ in range(n)]
    for i, j, g in darts:
        base_a = i * N
        base_b = aN + j * N
        for x in range(N):
            u = base_a + x
            v = base_b + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _reach(adj, src, D, n):
    """Number of vertices within distance D of src (src included)."""
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
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _fiber_cost(a, N, D, darts, T):
    """Unreached (fiber representative, vertex) pairs; zero iff diameter <= D.

    Uses the left-invariance of the lift: one BFS per fiber representative suffices.
    """
    n = 2 * a * N
    adj = _adjacency(a, N, darts, T)
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    return sum(n - _reach(adj, s, D, n) for s in sources)


def _init_darts(a, N, d, rng):
    """Random dart set: each A fiber has d darts, each B fiber receives exactly d."""
    slots = [j for j in range(a) for _ in range(d)]
    for _ in range(100):
        rng.shuffle(slots)
        darts = []
        for i in range(a):
            for k in range(d):
                darts.append((i, slots[i * d + k], rng.randrange(N)))
        if len(set(darts)) == len(darts):
            return darts
    return None


def _anneal(a, N, d, D, T, rng, deadline):
    """Anneal over dart sets to zero unreached pairs. Moves keep all fiber degrees."""
    darts = _init_darts(a, N, d, rng)
    if darts is None:
        return None
    cur = _fiber_cost(a, N, D, darts, T)
    for it in range(ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        new = list(darts)
        p = rng.randrange(len(new))
        if rng.random() < 0.6:
            # Swap B-targets of two darts: preserves B-degrees and A-degrees.
            q = rng.randrange(len(new))
            if q == p:
                continue
            i1, j1, g1 = new[p]
            i2, j2, g2 = new[q]
            new[p] = (i1, j2, g1)
            new[q] = (i2, j1, g2)
        else:
            # Re-randomise the group element of one dart.
            i, j, _ = new[p]
            new[p] = (i, j, rng.randrange(N))
        if len(set(new)) != len(new):
            continue
        v = _fiber_cost(a, N, D, new, T)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = new, v
    if cur == 0:
        return darts
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a until a valid dart set is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups:
        if time.monotonic() >= deadline:
            break
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _anneal(a, N, d, D, T, rng, deadline)
        if darts is not None:
            return darts, T
    return None


def _edges(a, N, darts, T):
    """Explicit edge list of the lift: A fibers are 0..aN-1, B fibers follow."""
    aN = a * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return edges


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

    moore = lib.moore_bound(d, D)

    # Candidate (total order, a, N) triples, ascending by total order.
    cands = []
    for a in range(1, MAX_A + 1):
        lo = max(2, -(-d // a))
        hi = moore // (2 * a)
        for N in range(lo, hi + 1):
            cands.append((2 * a * N, a, N))
    cands.sort()

    W = WINDOW0
    while time.monotonic() < deadline:
        # Only orders strictly above the current best are useful.
        window = [c for c in cands if c[0] > best_n][:W]
        if not window:
            break
        rng.shuffle(window)
        success = False
        for tot, a, N in window:
            rem = deadline - time.monotonic()
            if rem <= 0.2:
                break
            per = max(0.3, min(6.0, rem / (2 * len(window) + 1)))
            att_deadline = min(deadline, time.monotonic() + per)
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is None:
                continue
            darts, T = res
            consider(2 * a * N, _edges(a, N, darts, T))
            success = True
            break
        if not success:
            W = min(W + 4, WINDOW_MAX)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
