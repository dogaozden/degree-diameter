import math
import random
import time

import lib

ITERS = 400            # annealing steps per (group, base-graph) try
T_HOT = 4.0            # initial annealing temperature (unreached-pair units)
T_COLD = 0.3           # final annealing temperature
GROUPS_PER_ATTEMPT = 10
S_CHOICES = (2, 3, 1, 4)   # base-graph sizes per side, cycled through the search
MAX_BUDGET = 15.0


# ----------------------------------------------------------------------------
# Baseline families (always validated with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Generalized voltage lifts over small non-abelian groups.
#
# Base graph: s A-vertices and s B-vertices, with d darts leaving each A-vertex
# and entering each B-vertex. A dart (i, j, g) joins A(i, x) to B(j, x*g) for
# every group element x. Left multiplication is an automorphism of the lift, so
# eccentricities only need to be checked from one source per base vertex.
# Total order = 2 * s * N, where N = |G|.
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


def _cost(s, N, darts, T, invs, D):
    """Total unreached (source, vertex) pairs over one source per base vertex."""
    adjA = [[] for _ in range(s)]
    adjB = [[] for _ in range(s)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, invs[g]))
    V = 2 * s * N
    total = 0
    for src in range(2 * s):
        seen = bytearray(V)
        s0 = src * N
        seen[s0] = 1
        count = 1
        frontier = [s0]
        for _ in range(D):
            nxt = []
            for u in frontier:
                b, x = divmod(u, N)
                if b < s:
                    row = T[x]
                    for j, g in adjA[b]:
                        v = (s + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j = b - s
                    for i, gi in adjB[j]:
                        v = i * N + T[x][gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(s, N, d, D, T, invs, rng, iters, deadline):
    """Anneal voltages and B-endpoints of the base darts; return darts with zero cost or None."""
    E = s * d
    darts = []
    used = set()
    for _ in range(d):
        perm = list(range(s))
        rng.shuffle(perm)
        for i in range(s):
            j = perm[i]
            g = rng.randrange(N)
            while (i, j, g) in used:
                g = rng.randrange(N)
            used.add((i, j, g))
            darts.append((i, j, g))

    cur = _cost(s, N, darts, T, invs, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        if rng.random() < 0.6:
            # Voltage move on one dart.
            e = rng.randrange(E)
            i, j, g = darts[e]
            g2 = rng.randrange(N)
            if g2 == g or (i, j, g2) in used:
                continue
            darts[e] = (i, j, g2)
            used.discard((i, j, g))
            used.add((i, j, g2))
            v = _cost(s, N, darts, T, invs, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[e] = (i, j, g)
                used.discard((i, j, g2))
                used.add((i, j, g))
        else:
            # Swap B-endpoints of two darts (keeps all degrees).
            e1, e2 = rng.randrange(E), rng.randrange(E)
            i1, j1, g1 = darts[e1]
            i2, j2, g2 = darts[e2]
            if j1 == j2:
                continue
            old1, old2 = (i1, j1, g1), (i2, j2, g2)
            n1, n2 = (i1, j2, g1), (i2, j1, g2)
            if n1 in used or n2 in used:
                continue
            darts[e1], darts[e2] = n1, n2
            used.discard(old1)
            used.discard(old2)
            used.add(n1)
            used.add(n2)
            v = _cost(s, N, darts, T, invs, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[e1], darts[e2] = old1, old2
                used.discard(n1)
                used.discard(n2)
                used.add(old1)
                used.add(old2)
    if cur == 0:
        return darts
    return None


def _attempt(s, N, d, D, rng, deadline):
    """Try groups of order N for base size s; return (N, darts, T) on success."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(s, N, d, D, T, invs, rng, ITERS, deadline)
        if darts is not None:
            return N, darts, T
    return None


def _edges(s, N, darts, T):
    """Expand base darts into the full lift; return (n, edges)."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (s + j) * N + T[x][g]))
    return 2 * s * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2:
        return best

    # Binary-style search over total order, using lifts of random base graphs.
    lo = best[0]
    hi = lib._moore_bound(d, D)
    budget = 3.0
    step = 0
    while lo < hi and time.monotonic() < deadline - 1.0:
        target = (lo + hi + 1) // 2
        s = S_CHOICES[step % len(S_CHOICES)]
        step += 1
        if 2 * s > target:
            s = 1
        N = -(-target // (2 * s))
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(s, N, d, D, rng, att_deadline)
        if res is None:
            if time.monotonic() >= deadline:
                break
            hi = target - 1
            budget = min(budget * 1.3, MAX_BUDGET)
            continue
        N2, darts, T = res
        n, edges = _edges(s, N2, darts, T)
        if lib.is_valid(n, edges, d, D):
            if n > best[0]:
                best = (n, edges)
            lo = max(lo, n)
            budget = max(3.0, budget * 0.9)
        else:
            hi = target - 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
