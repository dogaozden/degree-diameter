import math
import random
import time

import lib

# New idea: a 2x2 base-graph voltage lift over semidirect groups. The graph has
# four orbits (A0, A1, B0, B1), each of size N = |G|. Dart (i, j, g) joins
# A_{i,x} to B_{j,x*g}. Left multiplication is an automorphism, so the diameter
# check needs only four BFS sources. The dart multiset is annealed. The parent's
# single-orbit bi-Cayley search is kept as a fallback for the first phase.

ITERS1 = 600      # annealing steps for the single-orbit search
ITERS4 = 250      # annealing steps for the four-orbit search
T_HOT = 1.5
T_COLD = 0.15


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


def _prepare(m, k, r):
    """Multiplication table and inverse list for the semidirect product (identity is element 0)."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return T, invs


def _bfs_cost(nb, sources, V, D):
    """Total number of (source, vertex) pairs not reached within D steps."""
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nb[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


# ----------------------------------------------------------------------------
# Single-orbit bi-Cayley search (phase 1, the parent's construction).
# ----------------------------------------------------------------------------

def _nb1(N, T, invs, S):
    Sinv = [invs[g] for g in S]
    nb = [None] * (2 * N)
    for x in range(N):
        nb[x] = [N + T[x][g] for g in S]
    for y in range(N):
        nb[N + y] = [T[y][h] for h in Sinv]
    return nb


def _anneal1(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _bfs_cost(_nb1(N, T, invs, S), (0, N), 2 * N, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _bfs_cost(_nb1(N, T, invs, S2), (0, N), 2 * N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _try_1orbit(N, d, D, rng, deadline, max_groups):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:max_groups]:
        if time.monotonic() > deadline:
            return None
        T, invs = _prepare(m, k, r)
        S = _anneal1(N, T, invs, d, D, rng, ITERS1, deadline)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            return 2 * N, edges
    return None


# ----------------------------------------------------------------------------
# Four-orbit voltage lift (phase 2, new).
# Blocks blk[i][j] hold distinct group elements g for darts A_i -> B_j.
# Block sizes: (0,0)=a, (0,1)=d-a, (1,0)=d-a, (1,1)=a. Every vertex has degree d.
# ----------------------------------------------------------------------------

def _nb4(N, T, invs, blk):
    V = 4 * N
    nb = [None] * V
    for i in (0, 1):
        for x in range(N):
            row = T[x]
            nb[i * N + x] = [2 * N + j * N + row[g] for j in (0, 1) for g in blk[i][j]]
    for j in (0, 1):
        for y in range(N):
            row = T[y]
            nb[2 * N + j * N + y] = [i * N + row[invs[g]] for i in (0, 1) for g in blk[i][j]]
    return nb


def _anneal4(N, T, invs, d, D, rng, iters, deadline):
    a = rng.randint(1, d - 1)
    sizes = [[a, d - a], [d - a, a]]
    blk = [[rng.sample(range(N), sizes[i][j]) for j in (0, 1)] for i in (0, 1)]
    srcs = (0, N, 2 * N, 3 * N)
    cur = _bfs_cost(_nb4(N, T, invs, blk), srcs, 4 * N, D)
    cells = [(i, j) for i in (0, 1) for j in (0, 1)]
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(cells)
        lst = blk[i][j]
        g = rng.randrange(N)
        if g in lst:
            continue
        pos = rng.randrange(len(lst))
        old = lst[pos]
        lst[pos] = g
        v = _bfs_cost(_nb4(N, T, invs, blk), srcs, 4 * N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[pos] = old
    return blk if cur == 0 else None


def _try_4orbit(N, d, D, rng, deadline, max_groups):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:max_groups]:
        if time.monotonic() > deadline:
            return None
        T, invs = _prepare(m, k, r)
        blk = _anneal4(N, T, invs, d, D, rng, ITERS4, deadline)
        if blk is not None:
            edges = []
            for i in (0, 1):
                for x in range(N):
                    for j in (0, 1):
                        for g in blk[i][j]:
                            edges.append((i * N + x, 2 * N + j * N + T[x][g]))
            return 4 * N, edges
    return None


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if best[0] > 1:
            return best

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    Moore = lib._moore_bound(d, D)

    # Phase 1: single-orbit bi-Cayley search, descending from the top.
    # This secures a fallback near the record.
    phase1_end = t0 + 0.35 * time_limit
    top1 = min(Moore // 2, Moore // 4 + 6)
    for N in range(top1, d, -1):
        if time.monotonic() >= min(phase1_end, end):
            break
        res = _try_1orbit(N, d, D, rng, min(phase1_end, end), 8)
        if res is not None:
            consider(*res)
            break

    # Phase 2: four-orbit voltage lift, ascending from just above the current best.
    Nmax4 = Moore // 4
    lo = max(d + 1, best[0] // 4 + 1)
    for N in range(lo, Nmax4 + 1):
        if time.monotonic() >= end:
            break
        res = _try_4orbit(N, d, D, rng, end, 3)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
