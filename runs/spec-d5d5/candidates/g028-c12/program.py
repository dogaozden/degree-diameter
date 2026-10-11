import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 16   # groups tried per order N within one attempt
ITERS = 2500                  # annealing steps per (group, block pattern) try


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New idea: two-orbit bi-Cayley lift (a 2+2 base graph over a group G).
#
# Vertices: A_{i,g} and B_{j,h} for i, j in {0, 1} and g, h in G (|G| = N).
# Connection blocks S_ij, subsets of G. Edge A_{i,g} -- B_{j,g*s} for s in S_ij.
# Block sizes: |S00| = |S11| = x, |S01| = |S10| = d - x, so every vertex has degree d.
# The graph has 4N vertices and is bipartite by construction.
#
# Left multiplication by G is an automorphism, so eccentricities need only four
# sources A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}. The annealing cost is the total
# number of (source, vertex) pairs at distance more than D, computed by BFS.
# ----------------------------------------------------------------------------

def _groups(N, cache):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in cache:
        return list(cache[N])
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    cache[N] = out
    return list(out)


def _cost(N, mulT, invs, S, D):
    """Total unreached (source, vertex) pairs over the four block sources."""
    twoN = 2 * N
    full = 4 * N
    # A-side: from A_i, neighbours are B_{j, g*s} for s in S[i][j].
    Aout = [[(j, s) for j in range(2) for s in S[i][j]] for i in range(2)]
    # B-side: from B_j, neighbours are A_{i, h*s^{-1}} for s in S[i][j].
    Bout = [[(i, invs[s]) for i in range(2) for s in S[i][j]] for j in range(2)]
    total = 0
    for src in (0, N, twoN, twoN + N):
        seen = bytearray(full)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < twoN:
                    i, g = divmod(u, N)
                    row = mulT[g]
                    for j, s in Aout[i]:
                        v = twoN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, h = divmod(u - twoN, N)
                    row = mulT[h]
                    for i, t in Bout[j]:
                        v = i * N + row[t]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += full - count
    return total


def _anneal(N, mulT, invs, d, D, rng, deadline):
    """Anneal the block sets to zero unreached pairs; return the sets or None."""
    x = rng.randint(1, d - 1)
    sizes = [[x, d - x], [d - x, x]]
    S = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
    cur = _cost(N, mulT, invs, S, D)
    for it in range(ITERS):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.02, 1.5 * (1.0 - it / ITERS))
        i = rng.randrange(2)
        j = rng.randrange(2)
        p = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = c
        v = _cost(N, mulT, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline, cache):
    """Try groups of order N until one gives a diameter-D two-orbit lift, or time runs out."""
    groups = _groups(N, cache)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        mulT = [[mul(g, s) for s in range(N)] for g in range(N)]
        invs = [inv(s) for s in range(N)]
        S = _anneal(N, mulT, invs, d, D, rng, deadline)
        if S is not None:
            return mulT, S
    return None


def _edges_from(N, d, mulT, S):
    """Edges of the 4N-vertex lift: A_{i,g} = i*N+g, B_{j,h} = 2N + j*N + h."""
    edges = []
    for i in range(2):
        for j in range(2):
            for s in S[i][j]:
                for g in range(N):
                    edges.append((i * N + g, 2 * N + j * N + mulT[g][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_total = max(0.3, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget_total
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

    # D = 1 with d >= 1: a single edge is the only option.
    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, q).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    if d < 2 or D < 2:
        return best

    # Two-orbit bi-Cayley search over semidirect products.
    Nmax = lib._moore_bound(d, D) // 4          # 4N vertices in the lift
    lo = max(d + 1, best_n // 4 + 1, Nmax // 3)
    hi = min(Nmax, (Nmax * 3) // 5)
    if lo > hi:
        return best

    cache = {}
    cands = list(range(lo, hi + 1))
    budget = 0.4
    while cands and time.monotonic() < deadline:
        i = 0
        while i < len(cands) and time.monotonic() < deadline:
            N = cands[i]
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(N, d, D, rng, att_deadline, cache)
            if res is None:
                i += 1
                continue
            mulT, S = res
            consider(4 * N, _edges_from(N, d, mulT, S))
            # Only larger orders can improve now.
            cands = [M for M in cands if M > N]
            i = 0
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
