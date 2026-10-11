"""Diameter-3 bipartite construction for the (d, D) cases.

Two families are combined:

1. Arc-extended projective plane graphs (the parent's family), built with a
   conic arc in PG(2, q) for the largest usable q.
2. Haar graphs H(Z_m, S) with |S| = d, which are bi-regular bipartite graphs
   of degree d and order 2m. For a Haar graph, diameter <= 3 holds exactly
   when S - S covers every nonzero residue of Z_m, so the search is a
   difference-cover problem. Since |S - S| <= d(d-1), we have m <= d^2 - d + 1,
   which matches the Moore bound 2(d^2 - d + 1) for D = 3.

The Haar search sweeps m downward from the Moore limit, spending a shrinking
slice of the time budget on each m with simulated annealing on S. The first
success is the largest m found. Every candidate is checked with lib.is_valid
before it can replace the current best, and K_{d,d} is the fallback.
"""
import math
import random
import time

import lib


def _arc_graph(d):
    """Conic-arc extension of PG(2, q) for the largest prime power q with spare degree >= 2."""
    best = None
    for q in range(2, d):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 2:
            continue
        F = lib.GF(q)
        pts = lib.projective_points(q)
        idx = {p: i for i, p in enumerate(pts)}
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        pl = [[] for _ in range(m)]   # lines through point P
        lp = [[] for _ in range(m)]   # points on line L
        for u, v in edges:
            pl[u].append(v - m)
            lp[v - m].append(u)
        S = [idx[(1, t, F.mul(t, t))] for t in range(q)] + [idx[(0, 0, 1)]]
        if q % 2 == 0:
            S.append(idx[(0, 1, 0)])
        cl = [0] * m
        cp = [0] * m
        for P in S:
            for L in pl[P]:
                cl[L] += 1
        for j in S:
            for Q in lp[j]:
                cp[Q] += 1
        if max(cl) > s or max(cp) > s:
            continue
        k = len(S)
        E = list(edges)
        for t, P in enumerate(S):
            x = 2 * m + t
            for L in pl[P]:
                E.append((x, m + L))
        for t, j in enumerate(S):
            b = 2 * m + k + t
            for Q in lp[j]:
                E.append((Q, b))
        n = 2 * m + 2 * k
        if best is None or n > best[0]:
            best = (n, E)
    return best


def _bump(S, cnt, unc, m, d, i, v, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between v and S[j], j != i."""
    for j in range(d):
        if j == i:
            continue
        s = S[j]
        for g in ((v - s) % m, (s - v) % m):
            if sign < 0:
                cnt[g] -= 1
                if cnt[g] == 0:
                    unc[0] += 1
            else:
                if cnt[g] == 0:
                    unc[0] -= 1
                cnt[g] += 1


def _cover(m, d, end, rng):
    """Find S = {0, s_1..s_{d-1}} in Z_m with S - S = Z_m, by annealing; None on timeout."""
    if m - 1 < d - 1:
        return None
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, m), d - 1)
        inS = [False] * m
        for s in S:
            inS[s] = True
        cnt = [0] * m
        for i in range(d):
            for j in range(d):
                if i != j:
                    cnt[(S[i] - S[j]) % m] += 1
        unc = [sum(1 for g in range(1, m) if cnt[g] == 0)]
        iters = 40000
        for it in range(iters + 1):
            if unc[0] == 0:
                return S
            if it == iters:
                break
            if it & 1023 == 0 and time.monotonic() >= end:
                return None
            T = max(0.08, 1.0 - 0.9 * it / iters)
            before = unc[0]
            i = rng.randrange(1, d)
            x = S[i]
            y = rng.randrange(1, m)
            while inS[y]:
                y = rng.randrange(1, m)
            _bump(S, cnt, unc, m, d, i, x, -1)
            S[i] = y
            _bump(S, cnt, unc, m, d, i, y, 1)
            delta = unc[0] - before
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                inS[x] = False
                inS[y] = True
            else:
                _bump(S, cnt, unc, m, d, i, y, -1)
                S[i] = x
                _bump(S, cnt, unc, m, d, i, x, 1)
    return None


def _haar_search(d, m_hi, m_lo, deadline, rng):
    """Sweep m downward from m_hi to m_lo; return (m, S) for the first success."""
    for m in range(m_hi, m_lo - 1, -1):
        now = time.monotonic()
        if now >= deadline:
            break
        per = (deadline - now) / (m - m_lo + 1)
        S = _cover(m, d, now + per, rng)
        if S is not None:
            return m, S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # D >= 3: arc-extended projective plane graph (diameter 3).
    arc = _arc_graph(d)
    if arc is not None and arc[0] > best[0] and lib.is_valid(arc[0], arc[1], d, D):
        best = arc

    # Haar graphs H(Z_m, S), |S| = d, diameter 3 iff S - S = Z_m.
    m_hi = d * d - d + 1
    m_lo = max(best[0] // 2 + 1, d + 1)
    if m_hi >= m_lo and time.monotonic() < deadline:
        res = _haar_search(d, m_hi, m_lo, deadline, rng)
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
