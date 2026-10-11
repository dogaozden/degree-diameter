import math
import random
import time

import lib

ITERS = 400              # annealing steps per (group, dart layout) try
GROUPS_PER_ATTEMPT = 4   # groups tried for one order N before moving on
ORBIT_COUNTS = (2, 2, 3, 4)  # number of A-orbits (= B-orbits) to sample from


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts over finite groups (non-bi-Cayley).
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. Each A_i has
# exactly d darts (i, j, g), each B_j receives exactly d darts, so the base is a
# d-regular bipartite multigraph. Lift: A_{i,x} ~ B_{j, x*g} for every dart.
# Left multiplication by any h is an automorphism, so the distance profile is
# determined by BFS from A_{i,e} and B_{j,e} (one source per orbit).
# Duplicate darts only lower degrees, which is still valid.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, i.e. Z_m x|_r Z_k (r=1 gives direct products)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(N, m, k, r):
    """Multiplication table T[x][y] and inverses for the group Z_m x|_r Z_k of order N."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _cost(N, b, D, T, invs, darts):
    """Number of (source, vertex) pairs at distance > D, over one source per orbit."""
    outs = [[] for _ in range(b)]
    ins = [[] for _ in range(b)]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, invs[g]))
    bN = b * N
    V = 2 * bN
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = bN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, h in ins[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, b, d, D, rng, T, invs, deadline, iters):
    """Anneal darts (voltages and B-endpoints) to zero unreached pairs; return darts or None."""
    darts = []
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            darts.append([i, perm[i], rng.randrange(N)])
    cur = _cost(N, b, D, T, invs, darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        cand = [row[:] for row in darts]
        if rng.random() < 0.6:
            p = rng.randrange(len(cand))
            cand[p][2] = rng.randrange(N)
        else:
            p = rng.randrange(len(cand))
            q = rng.randrange(len(cand))
            if p == q or cand[p][1] == cand[q][1]:
                continue
            # Swapping B-endpoints keeps every A row and every B column at d darts.
            cand[p][1], cand[q][1] = cand[q][1], cand[p][1]
        v = _cost(N, b, D, T, invs, cand)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            darts, cur = cand, v
    return darts if cur == 0 else None


def _edges(N, b, T, darts):
    """Edge list of the lift; vertices A_{i,x} = i*N+x and B_{j,y} = (b+j)*N+y."""
    bN = b * N
    E = set()
    for i, j, g in darts:
        for x in range(N):
            E.add((i * N + x, bN + j * N + T[x][g]))
    return 2 * bN, sorted(E)


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

    # Diameter 1 or degree 1: a single edge is the only connected option.
    consider(2, [(0, 1)])
    if D == 1 or d == 1:
        return best

    # D = 3 with d-1 a prime power: projective-plane incidence graph is optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    lo = {b: 2 for b in ORBIT_COUNTS}   # largest known-good group order per orbit count

    while time.monotonic() < deadline:
        live = [b for b in ORBIT_COUNTS if 2 * b * (lo[b] + 1) <= moore]
        if not live:
            break
        b = rng.choice(live)
        N = lo[b] + 1
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
            if time.monotonic() >= deadline:
                break
            T, invs = _table(N, m, k, r)
            darts = _anneal(N, b, d, D, rng, T, invs, deadline, ITERS)
            if darts is not None:
                found = (T, darts)
                break
        if found is not None:
            T, darts = found
            n, e = _edges(N, b, T, darts)
            before = best[0]
            consider(n, e)
            if best[0] > before or n > 0:
                lo[b] = N

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
