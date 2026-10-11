import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (D = 3, d - 1 a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW helper: bitset cyclic bi-Cayley evaluation.
#
# For the cyclic group Z_N, the bi-Cayley (Haar-type) graph with A_x ~ B_{x+s}
# (s in S, 0 in S WLOG) has vertex sets encoded as N-bit integers. Translating
# a set by s is a cyclic rotation, which costs two shifts and a mask, so a
# whole BFS layer is a handful of big-int operations. This is much faster than
# list-based BFS, so the hill climb can afford many more steps per order N.
# Left translation is an automorphism, so BFS from A_0 and B_0 suffices.
# ----------------------------------------------------------------------------

def _rot(X, s, N, FULL):
    """Map every bit x of X to bit (x + s) mod N."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & FULL


def _cyc_unreached(N, S, D):
    """Number of (source in {A_0, B_0}, vertex) pairs not within distance D."""
    FULL = (1 << N) - 1
    sinv = [(N - s) % N for s in S]
    total = 0
    for src_side in (0, 1):
        visA, visB = 0, 0
        if src_side == 0:
            visA = 1
            fA, fB = 1, 0
        else:
            visB = 1
            fA, fB = 0, 1
        for _ in range(D):
            nB = 0
            for s in S:
                nB |= _rot(fA, s, N, FULL)
            nA = 0
            for s in sinv:
                nA |= _rot(fB, s, N, FULL)
            nB &= ~visB
            nA &= ~visA
            if not (nA or nB):
                break
            visB |= nB
            visA |= nA
            fA, fB = nA, nB
        total += 2 * N - visA.bit_count() - visB.bit_count()
    return total


def _cyc_climb(N, d, D, rng, iters, stall_limit, deadline):
    """Hill-climb a cyclic connection set S (0 fixed in S) to zero unreached pairs."""
    if N < d:
        return None

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _cyc_unreached(N, S, D)

    S, cur = fresh()
    stall = 0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cyc_unreached(N, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > stall_limit:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Non-cyclic groups Z_m x|_r Z_k: general table-based bi-Cayley climb.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _gen_unreached(N, T, invs, S, D):
    """Unreached (source, vertex) pairs for the bi-Cayley graph A_x ~ B_{x g}, g in S."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _gen_climb(N, T, invs, d, D, rng, iters, stall_limit, deadline):
    """Hill-climb a connection set S in a non-cyclic group to zero unreached pairs."""
    if N < d:
        return None

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _gen_unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _gen_unreached(N, T, invs, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > stall_limit:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Parameters.
# ----------------------------------------------------------------------------

CYC_ITERS = 20000     # cyclic hill-climb steps per restart pool
CYC_STALL = 800       # restart after this many non-improving steps
GEN_ITERS = 1500
GEN_STALL = 300
N_WINDOW = 10         # candidate orders above the current lower bound
CYC_PROB = 0.7        # fraction of search effort on the fast cyclic path


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts with 2N vertices, N sweeping just above
    # the current record so every success raises the bar by a small step.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)

        if rng.random() < CYC_PROB:
            S = _cyc_climb(N, d, D, rng, CYC_ITERS, CYC_STALL, deadline)
            if S is not None:
                edges = [(x, N + (x + s) % N) for x in range(N) for s in S]
                consider(2 * N, edges)
        else:
            groups = [g for g in _groups(N) if g[1] > 1]
            if not groups:
                continue
            m, k2, r = rng.choice(groups)
            order, mul, inv = lib.semidirect_group(m, k2, r)
            T = [[mul(x, g) for g in range(order)] for x in range(order)]
            invs = [inv(g) for g in range(order)]
            S = _gen_climb(order, T, invs, d, D, rng,
                           GEN_ITERS, GEN_STALL, deadline)
            if S is not None:
                n_new, e_new = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
                consider(n_new, e_new)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
