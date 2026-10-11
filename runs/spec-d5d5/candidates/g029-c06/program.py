import math
import random
import time

import lib

ANNEAL_ITERS = 1500        # voltage moves per (group, base graph) try
GROUPS_PER_ATTEMPT = 6     # groups tried per (t, N) attempt
WINDOW = 16                # attempts pick among the lowest-order candidates in this window
MAX_T = 6                  # base graphs with t vertices on each side


# ----------------------------------------------------------------------------
# Baseline families (cheap; always validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over non-abelian groups.
#
# Base graph: t A-vertices and t B-vertices, d-regular bipartite multigraph
# built as a sum of d random permutation matrices (one dart per (k, i)).
# Each dart (i, j, g) lifts to the edges A_{i,x} -- B_{j, x*g} for all x in G.
# Vertices: A_{i,x} = i*N + x, B_{j,y} = (t + j)*N + y.
#
# Left multiplication by h in G is an automorphism of the lift, so it is
# transitive on each fibre. Hence eccentricities from the 2t representatives
# A_{i,e} and B_{j,e} decide the diameter exactly.
#
# Unlike the bi-Cayley case (t = 1), the base graph and voltages give a
# larger search space at the same group order, so orders above the record
# can be reached with small groups.
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


def _penalty(t, N, D, M, pairs, gs):
    """Number of (representative, vertex) pairs at distance > D in the lift."""
    V = 2 * t * N
    adj = [set() for _ in range(V)]
    for (i, j), g in zip(pairs, gs):
        base_a = i * N
        base_b = (t + j) * N
        for x in range(N):
            a = base_a + x
            b = base_b + M[x][g]
            adj[a].add(b)
            adj[b].add(a)
    adj = [list(s) for s in adj]

    total = 0
    for s in range(2 * t):
        src = s * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
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


def _anneal(t, N, D, M, pairs, rng, deadline):
    """Anneal the voltage of each dart to drive the penalty to zero."""
    P = len(pairs)
    gs = [rng.randrange(N) for _ in range(P)]
    cur = _penalty(t, N, D, M, pairs, gs)
    for it in range(ANNEAL_ITERS):
        if cur == 0:
            return gs
        if time.monotonic() > deadline:
            break
        k = rng.randrange(P)
        old = gs[k]
        gs[k] = rng.randrange(N)
        v = _penalty(t, N, D, M, pairs, gs)
        temp = max(0.2, 2.0 * (1.0 - it / ANNEAL_ITERS))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old
    return gs if cur == 0 else None


def _attempt(t, N, d, D, rng, deadline):
    """Try several groups of order N for base size t; return (M, pairs, gs) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() >= deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        M = [[mul(x, g) for g in range(N)] for x in range(N)]
        pairs = []
        for _ in range(d):
            perm = list(range(t))
            rng.shuffle(perm)
            pairs.extend((i, perm[i]) for i in range(t))
        gs = _anneal(t, N, D, M, pairs, rng, deadline)
        if gs is not None:
            return M, pairs, gs
    return None


def _edges(t, N, pairs, gs, M):
    """Expand the voltage lift into a deduplicated edge list."""
    es = set()
    for (i, j), g in zip(pairs, gs):
        for x in range(N):
            a = i * N + x
            b = (t + j) * N + M[x][g]
            es.add((a, b) if a < b else (b, a))
    return sorted(es)


def _pool(lo, hi, tmax=MAX_T):
    """Candidate (V, t, N) with lo < V = 2*t*N <= hi, sorted by V ascending."""
    out = []
    for t in range(1, tmax + 1):
        for N in range(max(1, lo // (2 * t)), hi // (2 * t) + 1):
            V = 2 * t * N
            if lo < V <= hi:
                out.append((V, t, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 5.0))
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

    # Exact record case for D = 3.
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

    bound = lib._moore_bound(d, D)   # bipartite Moore bound on vertex count
    attempts = 0

    while time.monotonic() < deadline and best_n < bound:
        lo = max(best_n, int(0.45 * bound))
        pool = _pool(lo, bound)
        if not pool:
            break
        V, t, N = pool[rng.randrange(min(WINDOW, len(pool)))]
        now = time.monotonic()
        budget = min(8.0, 1.0 * (1.08 ** attempts))
        attempts += 1
        res = _attempt(t, N, d, D, rng, min(deadline, now + budget))
        if res is not None:
            M, pairs, gs = res
            consider(2 * t * N, _edges(t, N, pairs, gs, M))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
