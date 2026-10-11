import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1 (D = 3): Haar graphs H(m, S) with |S| = d.
#
# H(m, S) has parts a_i, b_j (i, j in Z_m), a_i ~ b_{i+s} for s in S. It is
# bipartite and d-regular on 2m vertices. Two a-vertices a_i, a_j share a
# neighbour iff j - i lies in S - S. So if every nonzero residue is a
# difference of S, same-side pairs are at distance <= 2. Then S - S = Z_m,
# which also gives S + (S - S) + ... = Z_m, so opposite-side pairs are at
# distance <= 3. The condition is therefore exactly: S - S covers Z_m \ {0}.
# Since |S - S \ {0}| <= d(d-1), we have m <= d^2 - d + 1, i.e. n <= 2(d^2-d+1).
# For d = 16 that is 482, the ceiling. The search below looks for near-
# difference covers with simulated annealing on the number of uncovered residues.
# ----------------------------------------------------------------------------

def _haar_cost(S, m):
    """Number of nonzero residues of Z_m not expressed as a difference s - t of S."""
    cov = bytearray(m)
    for s in S:
        for t in S:
            cov[(s - t) % m] = 1
    return m - sum(cov)  # cov[0] is always set, so this counts uncovered nonzero residues


def _anneal_cover(d, m, rng, deadline, iters):
    """Anneal a size-d set S in Z_m (0 in S) whose difference set covers Z_m. Return S or None."""
    if m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = set(S)
    c = _haar_cost(S, m)
    T0, T1 = 1.5, 0.05
    for it in range(iters):
        if c == 0:
            break
        if (it & 511) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in inS:
            continue
        old = S[i]
        S[i] = x
        c2 = _haar_cost(S, m)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inS.discard(old)
            inS.add(x)
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def _search_cover(d, deadline, rng, consider):
    """Descend from the Moore-type modulus m = d^2 - d + 1 to the largest feasible m, then try upward."""
    mmax = d * d - d + 1
    m = mmax
    best_m = 0
    while m >= d + 1 and time.monotonic() < deadline:
        S = None
        for _ in range(2):
            S = _anneal_cover(d, m, rng, deadline, 6000)
            if S is not None:
                break
        if S is not None:
            best_m = m
            consider(*lib.haar_graph(m, S))
            break
        m -= 1
    if best_m == 0:
        return
    # Try to beat the found modulus, one step at a time.
    m = best_m + 1
    while m <= mmax and time.monotonic() < deadline:
        S = _anneal_cover(d, m, rng, deadline, 40000)
        if S is None and time.monotonic() < deadline:
            S = _anneal_cover(d, m, rng, deadline, 40000)
        if S is None:
            break
        consider(*lib.haar_graph(m, S))
        m += 1


# ----------------------------------------------------------------------------
# Family 2 (D >= 4): generic Haar hill-climb on bad_pairs (fallback family).
# ----------------------------------------------------------------------------

def _hill_bad(d, D, m, rng, deadline, iters):
    """Hill-climb a size-d set S in Z_m (0 in S) so that H(m, S) has diameter <= D."""
    if m - 1 < d - 1:
        return None

    def cost(S):
        n, e = lib.haar_graph(m, S)
        return lib.bad_pairs(n, e, D)

    S = [0] + rng.sample(range(1, m), d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_generic(d, D, rng, deadline, consider):
    m = d + 1
    while time.monotonic() < deadline:
        S = _hill_bad(d, D, m, rng, deadline, 150)
        if S is not None:
            consider(*lib.haar_graph(m, S))
        m += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        # Cycle of length 2D: bipartite, 2-regular, diameter D.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D == 3:
        # Projective plane incidence when d-1 is a prime power (Moore-optimal).
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
        _search_cover(d, deadline, rng, consider)
    else:
        _search_generic(d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
