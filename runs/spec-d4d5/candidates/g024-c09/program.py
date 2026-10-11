import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over non-abelian groups (Z_m x| Z_k), a family distinct from
# the annealed voltage lifts of the parent.
#
# Vertices: A_g = g and B_h = G + h for g, h in the group of order G.
# Connection set S with |S| = d (distinct elements). Edge A_g -- B_{g s}, s in S.
# Left multiplication is an automorphism, so distances only need to be checked
# from A_0 and B_0. Both sides are d-regular and the graph is bipartite.
# ----------------------------------------------------------------------------

def _pick_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G; returns (order, mul, inv) or None."""
    opts = []
    for k2 in range(1, G // 2 + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    if not opts:
        return None
    m, k2, r = rng.choice(opts)
    try:
        return lib.semidirect_group(m, k2, r)
    except ValueError:
        return None


def _bad(G, R, Iv, S, D):
    """Number of vertices not reached within distance D from A_0 and from B_0."""
    bad = 0
    N = 2 * G
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < G:
                    for s in S:
                        w = G + R[s][v]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    h = v - G
                    for s in S:
                        w = R[Iv[s]][h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += N - cnt
    return bad


def _anneal_S(G, R, Iv, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S; returns S with zero cost or None."""
    S = rng.sample(range(G), d)
    cost = _bad(G, R, Iv, S, D)
    T = 1.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _bad(G, R, Iv, T2, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
            S, cost = T2, c2
        T = max(0.2, T * 0.999)
    return S if cost == 0 else None


def _bicayley_edges(G, R, S):
    E = []
    for g in range(G):
        for s in S:
            E.append((g, G + R[s][g]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

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

    moore = lib._moore_bound(d, D)
    best = fallback

    # Projective plane incidence graph for D = 3 (meets the Moore bound when d-1 is a prime power).
    if D == 3:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            pg = lib.projective_plane_incidence(q)
            if pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
            if best[0] >= moore:
                return best

    # Bi-Cayley search: climb the group order G while annealing connection sets.
    try:
        bestG = d
        while time.monotonic() < deadline and 2 * bestG < moore:
            hi = max(bestG + 3, bestG + 1)
            G = bestG + 1 + rng.randrange(hi - bestG)
            G = min(G, moore // 2)
            if G < d:
                G = d
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                break
            slice_end = now + max(1.0, 0.25 * remaining)
            slice_end = min(slice_end, deadline)

            grp = _pick_group(G, rng)
            if grp is None:
                bestG += 1
                continue
            order, mul, inv = grp
            R = [[mul(g, s) for g in range(G)] for s in range(G)]
            Iv = [inv(s) for s in range(G)]
            S = _anneal_S(G, R, Iv, d, D, rng, slice_end, 20000)
            if S is not None:
                n, e = _bicayley_edges(G, R, S)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    bestG = G
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
