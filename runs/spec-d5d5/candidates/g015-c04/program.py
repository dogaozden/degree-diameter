import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 16   # groups tried per order N within one attempt
ITERS = 500                   # annealing steps per (group, block sizes) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
ORBITS = 2                    # orbits on each side (2 + 2 = 4 orbits in total)


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Two-orbit bi-Cayley search over semidirect products Z_m x|_r Z_k of order N.
#
# Vertices: A_{i,x} (i in {0,1}, x in G) and B_{j,y} (j in {0,1}, y in G),
# 4N vertices in total. For each block (i, j) we have a connection set S_ij
# and the edges A_{i,x} -- B_{j, x s} for s in S_ij. The block sizes form a
# 2x2 matrix [[a, d-a], [d-a, a]] with 1 <= a <= d-1, so every A and every B
# vertex has degree exactly d and every block is nonempty.
#
# Left multiplication by G is an automorphism, so distances from the four
# representatives A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e} decide the diameter.
# The search anneals over the connection sets to remove all unreached pairs.
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


def _unreached(N, T, invs, blocks, D):
    """Count (source, vertex) pairs not within distance D, over the four orbit representatives."""
    M = 4 * N
    # A_i row: forward moves to B_j via right-multiplication by s.
    Afw = [[(j, s) for j in range(ORBITS) for s in blocks[i][j]] for i in range(ORBITS)]
    # B_j row: backward moves to A_i via right-multiplication by s^{-1}.
    Bbw = [[(i, invs[s]) for i in range(ORBITS) for s in blocks[i][j]] for j in range(ORBITS)]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < 2 * N:
                    i = u // N
                    row = T[u - i * N]
                    for j, s in Afw[i]:
                        v = 2 * N + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    t = u - 2 * N
                    j = t // N
                    row = T[t - j * N]
                    for i, h in Bbw[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - count
    return total


def _anneal(N, T, invs, sizes, D, rng, iters, deadline):
    """Anneal the block connection sets to zero unreached pairs; return blocks or None."""
    blocks = [[rng.sample(range(N), sizes[i][j]) for j in range(ORBITS)] for i in range(ORBITS)]
    cells = [(i, j) for i in range(ORBITS) for j in range(ORBITS) if sizes[i][j] > 0]
    cur = _unreached(N, T, invs, blocks, D)
    for it in range(iters):
        if cur == 0:
            return blocks
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = cells[rng.randrange(len(cells))]
        blk = blocks[i][j]
        k = rng.randrange(len(blk))
        c = rng.randrange(N)
        if c in blk:
            continue
        old = blk[k]
        blk[k] = c
        v = _unreached(N, T, invs, blocks, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            blk[k] = old
    if cur == 0:
        return blocks
    return None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a valid two-orbit connection pattern, or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d - 1)
        sizes = [[a, d - a], [d - a, a]]
        blocks = _anneal(N, T, invs, sizes, D, rng, ITERS, deadline)
        if blocks is not None:
            return N, T, blocks
    return None


def _edges_from(N, T, blocks):
    """Expand the block connection sets into an explicit edge list on 4N vertices."""
    edges = []
    for i in range(ORBITS):
        for j in range(ORBITS):
            for s in blocks[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Four orbits in total, so the order is 4N and N is about Moore/4.
    Nmax = lib._moore_bound(d, D) // (2 * ORBITS)
    if Nmax < d:
        return best

    lo = d
    budget = 0.5
    while time.monotonic() < deadline and lo <= Nmax:
        success = False
        for N in range(lo, Nmax + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            if 2 * ORBITS * N <= best_n:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            N_ok, T, blocks = res
            consider(2 * ORBITS * N_ok, _edges_from(N_ok, T, blocks))
            lo = N_ok + 1
            success = True
            break
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
