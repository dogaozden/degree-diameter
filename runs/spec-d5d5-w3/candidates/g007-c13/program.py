import itertools
import math
import random
import time

import lib

KMAX = 16              # largest base-graph side k tried (base has k A-vertices and k B-vertices)
ITERS = 500            # annealing steps per restart
RESTARTS = 3           # fresh random voltage assignments per (k, group)
GROUPS_PER_CAND = 25   # groups tried per (k, N) candidate
PER_CAND_BUDGET = 2.0  # seconds spent on one (k, N) candidate before moving on


# ----------------------------------------------------------------------------
# Baseline families (cheap, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW family: k-orbit voltage lifts over semidirect products.
#
# Base graph: k A-vertices A_0..A_{k-1} and k B-vertices B_0..B_{k-1}.
# A_i is joined to B_{i+o} for each offset o in a set O of size d (0 in O, O in Z_k).
# Each such dart carries a voltage g in G (a finite group of order N, 0 = identity):
#     A_{i,x} -- B_{i+o, x*g}      for all i in Z_k, x in G.
# Total order 2kN, degree exactly d (k >= d so the offsets are distinct).
#
# Symmetry: left multiplication by G and the rotation i -> i+1 are automorphisms
# (with the same rotation applied to B), and they act transitively on A and on B.
# So the diameter is decided by BFS from A_{0,e} and B_{0,e} only.
# The voltage g_0 = identity WLOG (relabel B_{j,y} -> B_{j,y*h}).
# Setting k = 1 would recover the bi-Cayley search, so this generalizes it.
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
    """Multiplication and inverse tables for the group Z_m x|_r Z_k."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    MUL = [[mul(x, g) for g in range(N)] for x in range(N)]
    INV = [inv(g) for g in range(N)]
    return N, MUL, INV


def _unreached(k, N, MUL, INV, offs, volt, D):
    """Count (source, vertex) pairs not within distance D, for sources A_{0,e} and B_{0,e}."""
    kN = k * N
    V = 2 * kN
    fwd = list(zip(offs, volt))
    back = [(o, INV[g]) for o, g in fwd]
    total = 0
    for src in (0, kN):
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            if not frontier:
                break
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = MUL[x]
                    for o, g in fwd:
                        v = kN + ((i + o) % k) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = MUL[y]
                    for o, ig in back:
                        v = ((j - o) % k) * N + row[ig]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(k, N, MUL, INV, d, D, rng, iters, deadline):
    """Anneal offsets and voltages to make every pair within distance D."""
    offs = [0] + rng.sample(range(1, k), d - 1)
    volt = [0] + [rng.randrange(1, N) for _ in range(d - 1)]
    cur = _unreached(k, N, MUL, INV, offs, volt, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        o2, g2 = offs[:], volt[:]
        if rng.random() < 0.5:
            g2[i] = rng.randrange(1, N)
        else:
            c = rng.randrange(1, k)
            if c in offs:
                continue
            o2[i] = c
        v = _unreached(k, N, MUL, INV, o2, g2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            offs, volt, cur = o2, g2, v
    if cur == 0:
        return offs, volt
    return None


def _lift_edges(k, N, MUL, offs, volt):
    """Edge list of the k-orbit voltage lift: A_i -> index i*N+x, B_j -> index k*N+j*N+y."""
    kN = k * N
    edges = []
    for i in range(k):
        for x in range(N):
            for o, g in zip(offs, volt):
                edges.append((i * N + x, kN + ((i + o) % k) * N + MUL[x][g]))
    return edges


def _search(d, D, rng, deadline, floor_n):
    """Ascending search over (k, N) candidates; return the largest valid lift found above floor_n."""
    Mb = lib.moore_bound(d, D)
    pairs = []
    for k in range(d, KMAX + 1):
        for N in range(2, Mb // (2 * k) + 1):
            if 2 * k * N > floor_n:
                pairs.append((2 * k * N, k, N))
    pairs.sort()
    group_cache = {}
    best = None
    best_n = floor_n
    for size, k, N in pairs:
        if size <= best_n:
            continue
        now = time.monotonic()
        if now >= deadline:
            break
        cap = min(deadline, now + PER_CAND_BUDGET)
        if N not in group_cache:
            group_cache[N] = _groups(N)
        groups = group_cache[N][:]
        rng.shuffle(groups)
        found = None
        for m, kk, r in groups[:GROUPS_PER_CAND]:
            if time.monotonic() > cap:
                break
            _, MUL, INV = _tables(m, kk, r)
            for _ in range(RESTARTS):
                if time.monotonic() > cap:
                    break
                res = _anneal(k, N, MUL, INV, d, D, rng, ITERS, cap)
                if res is not None:
                    found = (res[0], res[1], MUL, INV)
                    break
            if found is not None:
                break
        if found is not None:
            offs, volt, MUL, INV = found
            edges = _lift_edges(k, N, MUL, offs, volt)
            n = 2 * k * N
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact record-matching case: incidence graph of PG(2, d-1).
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

    if D >= 2 and time.monotonic() < deadline:
        res = _search(d, D, rng, deadline, best[0])
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
