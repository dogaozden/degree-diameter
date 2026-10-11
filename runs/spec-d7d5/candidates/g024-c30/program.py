"""Bold variant: vertex-transitive bi-Cayley search.

Instead of multi-block voltage lifts (the parent's approach), this builds
bi-Cayley graphs with ONE block per side over many groups Z_m x| Z_k:
A_g ~ B_{g*s} for s in S, |S| = d. Left multiplication is an automorphism,
so diameter is certified by two BFS runs (from A_e and B_e), which makes each
candidate cheap to evaluate. Groups of order G (so n = 2G) are scanned upward
in G, with simulated annealing over S for each group. Every result is checked
with lib.is_valid. The fallback is K_{d,d} (valid for D >= 2); the exact
projective-plane incidence graph is used for D = 3 when it applies.

Risk: single-block lifts may not reach the orders of multi-block constructions,
so this path can fall short of the parent's score for the target case.
"""
import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _tables(m, k, r):
    """Multiplication table M[x, y] and inverses for Z_m x| Z_k, element a*k+b,
    (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    rinv = pow(r, -1, m)
    pwi = np.array([pow(rinv, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = ((-(pwi[b] * a)) % m) * k + (-b) % k
    return M, inv


def _groups_of_order(G, rng):
    """Candidate (m, k, r) with m*k = G, shuffled."""
    out = []
    for k in range(1, min(G, 40) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 12:
            rs = rng.sample(rs, 12)
        out.extend((m, k, r) for r in rs)
    rng.shuffle(out)
    return out


def _cost(S, M, inv, G, D):
    """Number of (source, vertex) pairs at distance > D, sources A_e and B_e."""
    colS = M[:, S]          # colS[g, j] = g * s_j       (A -> B)
    colI = M[:, inv[S]]     # colI[h, j] = h * s_j^{-1}  (B -> A)
    XA = np.zeros((2, G), dtype=bool)
    YB = np.zeros((2, G), dtype=bool)
    XA[0, 0] = True
    YB[1, 0] = True
    for _ in range(D):
        newX = XA.copy()
        newY = YB.copy()
        for row in (0, 1):
            ia = np.flatnonzero(XA[row])
            if ia.size:
                newY[row, colS[ia].ravel()] = True
            ib = np.flatnonzero(YB[row])
            if ib.size:
                newX[row, colI[ib].ravel()] = True
        XA, YB = newX, newY
    return 4 * G - int(XA.sum()) - int(YB.sum())


def _anneal(d, D, G, M, inv, rng, deadline, iters, patience):
    """Simulated annealing over S (|S| = d, distinct). Returns S or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    cost = _cost(S, M, inv, G, D)
    c0 = float(max(cost, 1))
    best = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.3, 0.05 * c0 * (1.0 - t / iters))
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        c2 = _cost(S, M, inv, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best = cost
                last = t
        else:
            S[j] = old
    return list(S) if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best_n, best_e

    # Scan group orders G (n = 2G) upward, equal time share per G.
    if (d, D) == (7, 5):
        lo, hi = 560, 610
    else:
        lo = best_n // 2 + 1
        hi = min(lo + 39, lib._moore_bound(d, D) // 2)
    Gs = [G for G in range(lo, hi + 1) if G >= d and 2 * G > best_n]

    for idx, G in enumerate(Gs):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(Gs) - idx)
        groups = _groups_of_order(G, rng)
        if not groups:
            continue
        found = None
        gi = 0
        while found is None and time.monotonic() < slice_end:
            m, k, r = groups[gi % len(groups)]
            gi += 1
            M, inv = _tables(m, k, r)
            S = _anneal(d, D, G, M, inv, rng, slice_end, 3000, 700)
            if S is not None:
                found = (M, S)
        if found is not None:
            M, S = found
            cols = M[:, S]
            edges = [(g, G + int(cols[g, j])) for g in range(G) for j in range(d)]
            consider(2 * G, edges)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
