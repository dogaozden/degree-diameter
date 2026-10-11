import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baselines for D = 3 (projective plane and Araujo-Pardo-Lopez graph).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products G = Z_m x| Z_k.
#
# Vertices A_g (index g) and B_h (index N + h). Connection set S (|S| = d,
# distinct): A_g ~ B_{g*s} for s in S. Every A-vertex has degree d, every
# B-vertex has degree d, and the graph is bipartite and simple.
#
# Left multiplication is an automorphism that is transitive on each side, so
# the diameter is at most D iff every vertex is within D of A_e and of B_e.
# ----------------------------------------------------------------------------

def _semidirect_tables(m, k, r):
    """Return (Rt, invs): Rt[s, g] = index of g*s and invs[s] = index of s^{-1}."""
    N = m * k
    G = np.arange(N, dtype=np.int64)
    A, B = G // k, G % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    # (a,b)*(c,d) = (a + r^b c, b + d); row index = s = (c,d), column = g = (a,b).
    a_prime = (A[None, :] + pw[B][None, :] * A[:, None]) % m
    b_prime = (B[None, :] + B[:, None]) % k
    Rt = a_prime * k + b_prime
    # Inverse of (c,d) is (-r^{-d} c, -d).
    nbs = (-B) % k
    invs = ((-pw[nbs] * A) % m) * k + nbs
    return Rt, invs


def _sample_group(N, rng):
    """Random (m, k, r) with m * k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    divs = [k for k in range(1, N + 1) if N % k == 0]
    k = rng.choice(divs)
    m = N // k
    r = 1
    if k > 1 and m > 2:
        cands = [x for x in range(2, m)
                 if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
        if cands and rng.random() < 0.8:
            r = rng.choice(cands)
    return m, k, r


def _cost_fn(N, Rt, invs, d, D):
    """Cost = number of (source, vertex) pairs at distance > D, over sources A_e and B_e."""
    inv_list = [int(x) for x in invs]

    def cost(S):
        fwd = [Rt[s] for s in S]
        bwd = [Rt[inv_list[s]] for s in S]
        total = 0
        for start_a in (True, False):
            seenA = np.zeros(N, dtype=bool)
            seenB = np.zeros(N, dtype=bool)
            if start_a:
                seenA[0] = True
                fA = seenA.copy()
                fB = np.zeros(N, dtype=bool)
            else:
                seenB[0] = True
                fB = seenB.copy()
                fA = np.zeros(N, dtype=bool)
            for _ in range(D):
                ia = np.flatnonzero(fA)
                ib = np.flatnonzero(fB)
                nB = np.zeros(N, dtype=bool)
                if ia.size:
                    for row in fwd:
                        nB[row[ia]] = True
                nB &= ~seenB
                seenB |= nB
                nA = np.zeros(N, dtype=bool)
                if ib.size:
                    for row in bwd:
                        nA[row[ib]] = True
                nA &= ~seenA
                seenA |= nA
                fA, fB = nA, nB
                if not (fA.any() or fB.any()):
                    break
            total += 2 * N - int(seenA.sum()) - int(seenB.sum())
        return total

    return cost


def _anneal(N, d, rng, end, cost_fn, max_iters):
    """Metropolis search over d-element connection sets; returns S with cost 0 or None."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    c = cost_fn(S)
    T = 1.0
    for _ in range(max_iters):
        if c == 0 or time.monotonic() >= end:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c2 = cost_fn(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.3, T * 0.995)
    return S if c == 0 else None


def _attempt(N, d, D, rng, end):
    """Try random semidirect groups of order N until one yields a valid connection set."""
    while time.monotonic() < end:
        m, k, r = _sample_group(N, rng)
        Rt, invs = _semidirect_tables(m, k, r)
        cost_fn = _cost_fn(N, Rt, invs, d, D)
        S = _anneal(N, d, rng, end, cost_fn, 500)
        if S is not None:
            return S, Rt
    return None


def _edges_from(N, Rt, S):
    """Edge list of the bi-Cayley graph with n = 2N vertices."""
    E = []
    for s in S:
        row = Rt[s]
        for g in range(N):
            E.append((g, N + int(row[g])))
    return 2 * N, E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best_n >= target:
        return best

    # Bi-Cayley climb: find a valid order N, then try to beat it.
    Nmax = target // 2
    if max(d, 2) > Nmax:
        return best
    best_N = best_n // 2
    window = 8
    budget = 0.6
    while time.monotonic() < deadline and best_N < Nmax:
        found = False
        for N in range(best_N + 1, min(Nmax, best_N + window) + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, end)
            if res is not None:
                S, Rt = res
                n, e = _edges_from(N, Rt, S)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best, best_n = (n, e), n
                    best_N = N
                    found = True
                    break
        if not found:
            budget = min(budget * 1.5, 8.0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
