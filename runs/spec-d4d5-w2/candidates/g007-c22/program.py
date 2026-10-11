import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family for the weakest target (d = 4, D = 5): single-orbit bi-Cayley
# graphs. Vertices A_g = g and B_x = G + x for g, x in a group of order G.
# Edges are A_g -- B_{g*s} for s in a connection set S of size d. Left
# multiplication is an automorphism, so the diameter check only needs BFS from
# A_e and B_e. Searching S by hill-climbing gives a fast cost, unlike the
# multi-layer annealing in the parent.
# ----------------------------------------------------------------------------

FRAC_TOTAL = 0.85
GCAP_MAX = 300          # keeps the multiplication table small
CLIMB_ITERS = 300
GROUPS_PER_G = 4


def _group_options(G):
    """All (m, k, r) with Z_m x| Z_k of order G = m*k, m >= 2."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _table(opt):
    """Return (order, M) with M[x][y] = x*y for the semidirect product (identity is 0)."""
    m, k, r = opt
    order, mul, _ = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    return order, M


def _missing(G, M, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_e and B_e."""
    adjA = [[G + M[g][s] for s in S] for g in range(G)]
    adjB = [[] for _ in range(G)]
    for g in range(G):
        row = M[g]
        for s in S:
            adjB[row[s]].append(g)
    total = 0
    N = 2 * G
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                nb = adjA[u] if u < G else adjB[u - G]
                for v in nb:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _climb(G, M, d, D, rng, iters, deadline):
    """Hill-climb a connection set S of size d with zero missing pairs; None if not found."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    c = _missing(G, M, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        x = rng.randrange(G)
        if x in S:
            continue
        i = rng.randrange(d)
        T = S[:]
        T[i] = x
        ct = _missing(G, M, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _attempt(G, d, D, rng, deadline):
    """Try a few random groups of order G; return a valid (n, edges) or None."""
    opts = _group_options(G)
    if not opts:
        return None
    rng.shuffle(opts)
    for opt in opts[:GROUPS_PER_G]:
        if time.monotonic() > deadline:
            break
        order, M = _table(opt)
        S = _climb(order, M, d, D, rng, CLIMB_ITERS, deadline)
        if S is None:
            continue
        E = [(g, order + M[g][s]) for g in range(order) for s in S]
        n = 2 * order
        if lib.is_valid(n, E, d, D):
            return n, E
    return None


def _bicayley_search(d, D, moore, rng, deadline, consider):
    """Descend from the largest admissible order until one works, then ascend."""
    Gcap = min(moore // 2, GCAP_MAX)
    Gmin = max(d, 2)
    G = Gcap
    found_G = None
    while G >= Gmin and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = now + max(0.5, 0.05 * (deadline - now))
        res = _attempt(G, d, D, rng, min(slice_end, deadline))
        if res is not None:
            consider(res)
            found_G = G
            break
        G -= 1
    if found_G is None:
        return
    G = found_G + 1
    fails = 0
    while G <= Gcap and time.monotonic() < deadline and fails < 3:
        now = time.monotonic()
        slice_end = now + max(0.5, 0.05 * (deadline - now))
        res = _attempt(G, d, D, rng, min(slice_end, deadline))
        if res is not None:
            consider(res)
            fails = 0
        else:
            fails += 1
        G += 1


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d}: diameter 2, always valid.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph (diameter 3, degree q+1 = d).
    try:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(lib.projective_plane_incidence(q))
                break
    except Exception:
        pass

    # Main new family: bi-Cayley search.
    try:
        if moore // 2 >= max(d, 2):
            _bicayley_search(d, D, moore, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
