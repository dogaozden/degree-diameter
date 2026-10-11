import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# Fallbacks: K_{d,d} (valid for D >= 2) and, for D = 3, the projective plane
# incidence graph PG(2, q) with q the largest prime power with q + 1 <= d.
#
# Main family (new in this version): Haar graphs over ABELIAN groups
# G = Z_a x Z_b with a single base block. Vertices A_g and B_h (g, h in G),
# A_g ~ B_{g+s} for s in S, |S| = d. Translation gives vertex transitivity on
# each side, so diameter <= D reduces to two covering conditions with
#   D_set = S - S (contains 0),  X_j = j-fold sumset of D_set:
#   A-side: X_{floor(D/2)} = G,     B-side: S + X_{floor((D-1)/2)} = G.
# Cost evaluation is a few small numpy sumsets (d*d and |X|*d sized), far cheaper
# than the bitmask reach used in the earlier bi-Cayley search. Simulated
# annealing over the d-1 non-identity elements of S (we may fix 0 in S by
# translation) minimises the number of uncovered group elements. Successful
# orders grow adaptively.
# ----------------------------------------------------------------------------


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sumset(P, Q, a, b, n):
    """Index set of {p + q} in Z_a x Z_b (index = ca*b + cb)."""
    pa, pb = P // b, P % b
    qa, qb = Q // b, Q % b
    res = (((pa[:, None] + qa[None, :]) % a) * b + (pb[:, None] + qb[None, :]) % b).ravel()
    mark = np.zeros(n, dtype=bool)
    mark[res] = True
    return np.flatnonzero(mark)


def _cost(S, a, b, n, L, Lp):
    """Number of uncovered group elements over both sides (0 means diameter <= D)."""
    sa, sb = S // b, S % b
    diff = (((sa[:, None] - sa[None, :]) % a) * b + (sb[:, None] - sb[None, :]) % b).ravel()
    Dl = np.unique(diff)  # contains 0
    X = np.zeros(1, dtype=np.int64)
    XLp = X
    for j in range(1, L + 1):
        X = _sumset(X, Dl, a, b, n)
        if j == Lp:
            XLp = X
    B = _sumset(S, XLp, a, b, n)
    return (n - len(X)) + (n - len(B))


def _anneal(a, b, d, D, rng, t_end):
    """Anneal a connection set S (|S| = d, 0 in S) in Z_a x Z_b. Returns S as array or None."""
    n = a * b
    if d < 2 or d > n:
        return None
    L = D // 2
    Lp = (D - 1) // 2
    S = [0] + rng.sample(range(1, n), d - 1)
    Sarr = np.array(S, dtype=np.int64)
    c = _cost(Sarr, a, b, n, L, Lp)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while c > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.05
        p = rng.randrange(1, d)
        x = rng.randrange(n)
        if x in S:
            continue
        old = S[p]
        S[p] = x
        Sarr[p] = x
        c2 = _cost(Sarr, a, b, n, L, Lp)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[p] = old
            Sarr[p] = old
    return Sarr if c == 0 else None


def _haar_edges(S, a, b, n):
    """Haar graph A_g ~ B_{g+s}: vertices A = 0..n-1, B = n..2n-1."""
    idx = np.arange(n, dtype=np.int64)
    ca, cb = idx // b, idx % b
    out = []
    for s in S.tolist():
        sa, sb = s // b, s % b
        nb = ((ca + sa) % a) * b + (cb + sb) % b
        out.extend(zip(idx.tolist(), (n + nb).tolist()))
    return 2 * n, out


def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact projective-plane construction for D = 3.
    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # Main search: Haar graphs over abelian groups Z_a x Z_b.
    best_side = best_n // 2
    step = 2
    while True:
        now = time.monotonic()
        if now >= deadline - 0.2:
            break
        target = best_side + rng.randint(1, step)
        if target < d:
            target = d
        if rng.random() < 0.5:
            a = target  # cyclic
        else:
            a = rng.choice(_divisors(target))
        b = target // a
        t_end = min(deadline, time.monotonic() + 4.0)
        S = _anneal(a, b, d, D, rng, t_end)
        if S is not None:
            n2, e2 = _haar_edges(S, a, b, target)
            if lib.is_valid(n2, e2, d, D):
                if n2 > best_n:
                    best = (n2, e2)
                    best_n = n2
                best_side = target
                step = min(step * 2, max(2, best_side // 25))
            else:
                step = max(1, step // 2)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
