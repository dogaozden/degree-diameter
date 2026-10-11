"""Bi-circulant (Haar graph) difference-cover search for diameter-3 bipartite graphs.

Haar graph H(m, S): vertices a_i, b_i (i in Z_m), edges a_i -- b_{i+s} for s in S, |S| = d.
It is bipartite and d-regular. For D = 3 it has diameter <= 3 iff S - S covers Z_m
(same-side pairs need a common neighbour) and S - S + S covers Z_m (opposite-side pairs).
So a valid graph with m > d*d - d + 1 is impossible, and d = 16 needs m >= 198 to beat 394.

Search: simulated annealing over the d-1 nonzero elements of S, for each m upward from a
starting guess. Each m uses bitmask rotations, so cost evaluation is fast. For D >= 4 a
generic BFS cost is used. Every candidate is checked with lib.is_valid before it is kept.
The fallback is K_{d,d}, which is valid for every D >= 2.
"""
import math
import random
import time

import lib


def _rot(x, s, m, full):
    """Cyclic shift of an m-bit set: element a maps to (a + s) mod m."""
    s %= m
    if s == 0:
        return x
    return ((x << s) | (x >> (m - s))) & full


def _cost3(S, m, full):
    """Uncovered count for diameter 3: (Z_m minus S-S) plus (Z_m minus S-S+S). Zero iff valid."""
    Sbits = 0
    for s in S:
        Sbits |= 1 << s
    DS = 0
    for b in S:
        DS |= _rot(Sbits, (m - b) % m, m, full)
    AB = 0
    for s in S:
        AB |= _rot(DS, s, m, full)
    return (m - DS.bit_count()) + (m - AB.bit_count())


def _costG(S, m, D):
    """Generic cost for any D: unreached pairs from a_0 and b_0 within distance D (zero iff valid)."""
    N = 2 * m
    adj = [[] for _ in range(N)]
    for s in S:
        for i in range(m):
            a, b = i, m + (i + s) % m
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in (0, m):
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal(d, D, m, rng, deadline):
    """Find S (|S| = d, contains 0, subset of Z_m) with zero cost, or return None at the deadline."""
    k = d
    if k > m:
        return None
    full = (1 << m) - 1
    if D == 3:
        def cost_fn(S):
            return _cost3(S, m, full)
    else:
        def cost_fn(S):
            return _costG(S, m, D)

    S = [0] + rng.sample(range(1, m), k - 1)
    c = cost_fn(S)
    R = 3000  # temperature cycle length
    it = 0
    while True:
        if c == 0:
            return sorted(S)
        if it % 256 == 0 and time.monotonic() > deadline:
            return None
        it += 1
        phase = it % R
        T = 1.0 * (0.02 ** (phase / R)) + 0.02
        i = rng.randrange(1, k)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = cost_fn(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return best

    rng = random.Random(seed)

    if D == 3:
        m_lo = max(d + 1, int(0.7 * (d * d - d + 1)))
        m_hi = d * d - d + 1  # Moore-type bound on m for diameter 3
    else:
        m_lo = d + 1
        m_hi = 400

    m = m_lo
    while m <= m_hi and time.monotonic() < deadline:
        S = _anneal(d, D, m, rng, deadline)
        if S is None:
            break  # deadline reached while searching this m
        n, e = lib.haar_graph(m, S)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
