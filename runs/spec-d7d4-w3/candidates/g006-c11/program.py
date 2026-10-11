import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over finite groups G (order g), with connection set S of
# size d. Vertices: A_x = x and B_y = g + y. Edge A_x -- B_{x*s} for s in S.
# Left multiplication by any group element is an automorphism, so the diameter
# is at most D iff every vertex is within distance D of A_0 and of B_0.
# Search: simulated annealing over S, with groups drawn from Z_m x| Z_k.
# This replaces the earlier twin-blow-up / cover-growth pipeline.
# ----------------------------------------------------------------------------

def _group_options(G, rng, count):
    """Candidate groups of order G as (m, k, r): Z_m x|_r Z_k, with r^k = 1 mod m."""
    cands = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            cands.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        pick = set(rng.sample(rs, min(len(rs), 3)))
        pick.add(1)
        for r in pick:
            cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:count]


def _cost(G, mt, invt, S, D):
    """Number of (source, vertex) pairs at distance > D from A_0 and B_0. Zero iff diameter <= D."""
    N = 2 * G
    Sinv = [invt[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = mt[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = mt[u - G]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal(G, mt, invt, d, D, rng, deadline, iters):
    """Anneal a d-element connection set S in the group so that the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    inS = set(S)
    cost = _cost(G, mt, invt, S, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = 2.0 * (0.05 / 2.0) ** (it / iters)
        x = rng.randrange(G)
        if x in inS:
            continue
        i = rng.randrange(d)
        old = S[i]
        S[i] = x
        c2 = _cost(G, mt, invt, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            inS.discard(old)
            inS.add(x)
            cost = c2
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _bicayley_edges(G, mt, S):
    E = []
    for g in range(G):
        row = mt[g]
        for s in S:
            E.append((g, G + row[s]))
    return 2 * G, E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph when d - 1 is a prime power.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        consider(n0, e0)
    if best[0] >= moore:
        return best

    # Bi-Cayley search: climb the group order from the middle of the Moore range.
    moore_half = moore // 2
    lo = max(d, int(0.5 * moore_half))
    while time.monotonic() < deadline:
        if lo > moore_half:
            break
        G = rng.randint(lo, min(moore_half, lo + 3))
        for (m, k, r) in _group_options(G, rng, 3):
            now = time.monotonic()
            if now >= deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            mt = [[mul(x, y) for y in range(order)] for x in range(order)]
            invt = [inv(x) for x in range(order)]
            slice_end = min(deadline, now + 2.0)
            S = _anneal(order, mt, invt, d, D, rng, slice_end, 3000)
            if S is not None:
                n, e = _bicayley_edges(order, mt, S)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    lo = max(lo, order + 1)
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
