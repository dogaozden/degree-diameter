import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   * PG(2,q) incidence and the Araujo-Pardo-Lopez graph (D = 3 only).
#   * Bi-Cayley graphs over groups G of order N (N = 313, 314, ...):
#       A_g joins B_{g s} for s in S, |S| = d.
#     The graph is invariant under left multiplication, so only two BFS runs
#     (from A_e and B_e) are needed to test diameter <= D exactly.
#   * The connection set S is found by annealing over group elements, with the
#     group itself drawn at random from all semidirect products Z_m x| Z_k of order N.
#     The search ascends N from the current best order, so it aims at 2N > best.
#   * Fallbacks: K_{d,d} (diameter 2), a cycle for d = 2, and an edge for d = 1.
#     Every candidate passes lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _groups_of_order(N, rng, max_r=30):
    """List (m, k, r) describing semidirect products Z_m x| Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            out.append((N, 1, 1))  # cyclic group
            continue
        if m == 1:
            out.append((1, k, 0))  # cyclic group of order k
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if len(cands) > max_r:
            cands = rng.sample(cands, max_r)
        out.extend((m, k, r) for r in cands)
    return out


def _maps(order, mul):
    """Lazily cached right-multiplication permutations and their inverses."""
    rm_cache = {}
    inv_cache = {}

    def rm(s):
        t = rm_cache.get(s)
        if t is None:
            t = [mul(g, s) for g in range(order)]
            rm_cache[s] = t
        return t

    def rinv(s):
        t = inv_cache.get(s)
        if t is None:
            base = rm(s)
            t = [0] * order
            for g, h in enumerate(base):
                t[h] = g
            inv_cache[s] = t
        return t

    return rm, rinv


def _unreached(N, D, S, rm, rinv):
    """Number of (source, vertex) pairs at distance > D, for sources A_e and B_e.

    Vertices: A_g = g (0..N-1), B_h = N + h. Zero means valid.
    """
    R = [rm(s) for s in S]
    I = [rinv(s) for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for row in R:
                        w = N + row[v]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    u = v - N
                    for row in I:
                        w = row[u]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, D, d, rm, rinv, rng, iters, deadline):
    """Annealing over connection sets S of size d in a group of order N."""
    S = rng.sample(range(N), d)
    c = _unreached(N, D, S, rm, rinv)
    best_c, best_S = c, list(S)
    T = 1.0
    for it in range(iters):
        if best_c == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _unreached(N, D, S, rm, rinv)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
            if c < best_c:
                best_c, best_S = c, list(S)
        else:
            S[i] = old
        T = max(0.05, T * 0.995)
    return best_c, best_S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        if best_n >= moore:
            return best  # already optimal (e.g. PG(2,2) for d=3, D=3)

    # Group search: ascend through orders N, looking for 2N > best_n.
    N = max(best_n // 2 + 1, int(0.4 * moore / 2))
    tries_per_N = 4
    iters = 400
    while time.monotonic() < deadline and 2 * N <= moore:
        N = max(N, best_n // 2 + 1)
        groups = _groups_of_order(N, rng)
        if groups:
            for _ in range(tries_per_N):
                if time.monotonic() >= deadline:
                    break
                m, k, r = rng.choice(groups)
                try:
                    order, mul, _ = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                if order != N:
                    continue
                rm, rinv = _maps(order, mul)
                c, S = _climb(N, D, d, rm, rinv, rng, iters, deadline)
                if c == 0:
                    edges = [(g, N + rm(s)[g]) for s in S for g in range(N)]
                    consider(2 * N, edges)
                    break
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
