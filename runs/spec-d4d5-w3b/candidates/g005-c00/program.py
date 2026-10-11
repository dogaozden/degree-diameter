import math
import random
import time

import lib


def _bad(G, S, Tm, Im, D):
    """Count (source, vertex) pairs not reached within D steps, sources = (0,e) and (1,e).

    Vertices: side 0 is g in [0, G), side 1 is G + x. Edge (0,g)-(1,g*s) for s in S.
    Left multiplication is an automorphism on each side, so these two sources suffice.
    """
    N = 2 * G
    invS = [Im[s] for s in S]
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
                    row = Tm[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = Tm[u - G]
                    for si in invS:
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


def _climb(G, d, D, Tm, Im, rng, steps, deadline):
    """Hill-climb a d-element connection set S in the group so the bi-Cayley graph has diameter <= D."""
    S = rng.sample(range(G), d)
    c = _bad(G, S, Tm, Im, D)
    for it in range(steps):
        if c == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _bad(G, T, Tm, Im, D)
        if ct <= c or rng.random() < 0.01:
            S, c = T, ct
    return S if c == 0 else None


def _groups(G, rng, cap=6):
    """Candidate groups of order G as (m, k, r) for Z_m x| Z_k; the cyclic group comes first."""
    opts = []
    for k in range(2, G):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    rng.shuffle(opts)
    return [(G, 1, 1)] + opts[:cap]


def _tables(G, spec):
    m, k, r = spec
    order, mul, inv = lib.semidirect_group(m, k, r)
    Tm = [[mul(x, y) for y in range(G)] for x in range(G)]
    Im = [inv(x) for x in range(G)]
    return Tm, Im


def _graph(G, S, Tm):
    edges = [(g, G + Tm[g][s]) for g in range(G) for s in S]
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    # Projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = fallback
    best_n = fallback[0]

    # Bold family: bi-Cayley graphs over groups Z_m x| Z_k, each side indexed by the group.
    # Each graph is d-regular with 2G vertices; we scan the group order G upward.
    lo = max(d + 1, lib.moore_bound(d, D) // 4)
    G = lo
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, (deadline - now) / 8.0))
        found = None
        for spec in _groups(G, rng):
            if time.monotonic() > slice_end:
                break
            Tm, Im = _tables(G, spec)
            S = _climb(G, d, D, Tm, Im, rng, 2500, slice_end)
            if S is not None:
                found = (S, Tm)
                break
        if found is not None:
            S, Tm = found
            n, edges = _graph(G, S, Tm)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
            fails = 0
        else:
            fails += 1
        G += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
