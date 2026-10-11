import math
import random
import time
import itertools

import lib

# Bold change: instead of a single-orbit bi-Cayley graph (base = 1 vertex per side),
# search voltage lifts over a base multigraph with p vertices per side. Each base
# A_i -- B_j pair carries a multiset of group labels, and the lift over a group G
# of order N has 2*p*N vertices. Left multiplication by G is an automorphism, so
# reaching all vertices within distance D from the 2p class representatives
# (A_{i,e}, B_{j,e}) certifies diameter <= D.

ITERS = 500            # annealing steps per (group, base) try
GROUPS_PER_N = 8       # groups tried per (p, N) before moving on
T_HOT = 2.0            # initial temperature (unreached-pair units)
T_COLD = 0.2           # final temperature
P_CHOICES = [1, 2, 2, 3, 3, 4]


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _complete_bipartite(d):
    """K_{d,d}: diameter 2, degree d, order 2d."""
    edges = [(a, d + b) for a in range(d) for b in range(d)]
    return 2 * d, edges


# ----------------------------------------------------------------------------
# Multi-vertex voltage lifts over semidirect products Z_m x|_r Z_k.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for the group."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return T, invs


def _random_base(p, d, rng):
    """p x p nonnegative integer matrix with all row and column sums equal to d."""
    M = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            M[i][perm[i]] += 1
    return M


def _cost(p, N, D, T, invs, darts, sources, V):
    """Total number of (source, vertex) pairs not within distance D, over class representatives."""
    outs = [[] for _ in range(p)]
    ins = [[] for _ in range(p)]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, invs[g]))
    PN = p * N
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < PN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = PN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - PN, N)
                    row = T[y]
                    for i, h in ins[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(p, N, d, D, T, invs, M, rng, deadline):
    """Anneal the group labels on the darts of base matrix M to zero the unreached count."""
    darts = []
    for i in range(p):
        for j in range(p):
            if M[i][j]:
                for g in rng.sample(range(N), M[i][j]):
                    darts.append((i, j, g))
    sources = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    V = 2 * p * N
    cur = _cost(p, N, D, T, invs, darts, sources, V)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(len(darts))
        i, j, g = darts[t]
        forb = {g2 for (i2, j2, g2) in darts if i2 == i and j2 == j}
        if len(forb) >= N:
            continue
        c = rng.randrange(N)
        while c in forb:
            c = rng.randrange(N)
        old = darts[t]
        darts[t] = (i, j, c)
        v = _cost(p, N, D, T, invs, darts, sources, V)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[t] = old
    return darts if cur == 0 else None


def _try_order(p, N, d, D, rng, deadline):
    """Try several groups of order N and random base matrices; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(m, k, r)
        M = _random_base(p, d, rng)
        darts = _anneal(p, N, d, D, T, invs, M, rng, deadline)
        if darts is not None:
            return T, darts
    return None


def _lift_edges(p, N, T, darts):
    """Expand darts into the full lifted edge list on 2*p*N vertices."""
    PN = p * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, PN + j * N + T[x][g]))
    return 2 * PN, edges


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

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)

    # Safe fallback: K_{d,d} has diameter 2 (valid for every D >= 2).
    consider(*_complete_bipartite(d))

    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except ValueError:
            pass

    if best[0] >= moore or d <= 2 or D <= 2:
        return best

    # Search over voltage lifts with p base vertices per side.
    while time.monotonic() < deadline:
        if best[0] >= moore:
            break
        p = rng.choice(P_CHOICES)
        Nmax = moore // (2 * p)
        lo = best[0] // (2 * p) + 1
        if lo > Nmax:
            # This p cannot beat the current best; check whether any p can.
            if all(best[0] // (2 * q) + 1 > moore // (2 * q) for q in range(1, 5)):
                break
            continue
        hi = min(Nmax, lo + 40)
        N = lo + int(rng.expovariate(0.3))
        N = max(d, min(N, hi))
        if N > Nmax:
            continue

        res = _try_order(p, N, d, D, rng, deadline)
        if res is None:
            continue
        T, darts = res
        n, e = _lift_edges(p, N, T, darts)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
