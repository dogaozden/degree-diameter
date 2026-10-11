import math
import random
import time

import lib

ITERS = 500              # annealing steps per (group, base, order) try
PER_TRY = 1.5           # seconds allowed for one annealing try
MAX_GROUPS = 10         # groups tried for one (k, N) choice
T_HOT = 2.0             # initial annealing temperature (in unreached-pair units)
T_COLD = 0.1            # final annealing temperature


# ----------------------------------------------------------------------------
# Base families (fast fallbacks; every result is checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Generalized voltage lifts over finite groups Z_m x| Z_k.
#
# Base graph: k "A" vertices and k "B" vertices. The base is d-regular bipartite,
# built as the union of d permutations pi_t of range(k). Dart (i, pi_t(i), g)
# carries a group voltage g. Lift vertices: A(i, x) and B(j, y), x, y in G.
# Edge A(i, x) -- B(j, x*g) for every dart (i, j, g).
#
# Left multiplication by h is an automorphism of the lift, so every vertex's
# eccentricity equals one of the 2k eccentricities at A(i, e) or B(j, e).
# Parallel darts (same i, j) need distinct voltages so the lift stays simple
# and d-regular.
#
# This differs from a single bi-Cayley graph: the base has k >= 2 vertices per
# side, which adds freedom and gives orders 2kN with N in a different range.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
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
    """Multiplication table M[x][g] = x*g and inverse table for the group Z_m x|_r Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, g) for g in range(order)] for x in range(order)]
    I = [inv(g) for g in range(order)]
    return order, M, I


def _tables_from(darts, k, I):
    """Per-A-vertex dart lists and per-B-vertex dart lists (with inverse voltages)."""
    Ad = [[] for _ in range(k)]
    Bd = [[] for _ in range(k)]
    for i, j, g in darts:
        Ad[i].append((j, g))
        Bd[j].append((i, I[g]))
    return Ad, Bd


def _unreached(k, N, M, Ad, Bd, D):
    """Count (source, vertex) pairs at distance > D, over the 2k base-vertex sources."""
    total_v = 2 * k * N
    base_B = k * N
    total = 0
    for s in range(2 * k):
        if s < k:
            src = s * N
        else:
            src = base_B + (s - k) * N
        seen = bytearray(total_v)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base_B:
                    i, x = divmod(u, N)
                    row = M[x]
                    for j, g in Ad[i]:
                        v = base_B + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base_B, N)
                    row = M[y]
                    for i, gi in Bd[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += total_v - count
    return total


def _anneal(k, N, M, I, d, D, rng, iters, deadline):
    """Anneal voltages on a random d-regular bipartite base to reach diameter <= D.

    Returns the list of darts (i, j, g) on success, otherwise None.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, perms[t][i], 0] for i in range(k) for t in range(d)]

    # Initial voltages: distinct among parallel darts with the same (i, j).
    for idx in range(len(darts)):
        i, j, _ = darts[idx]
        used = {darts[q][2] for q in range(idx)
                if darts[q][0] == i and darts[q][1] == j}
        free = [g for g in range(N) if g not in used]
        if not free:
            return None
        darts[idx][2] = rng.choice(free)

    Ad, Bd = _tables_from(darts, k, I)
    cur = _unreached(k, N, M, Ad, Bd, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        a = rng.randrange(len(darts))
        i, j, old = darts[a]
        g = rng.randrange(N)
        if g == old:
            continue
        clash = False
        for q in range(len(darts)):
            if q != a and darts[q][0] == i and darts[q][1] == j and darts[q][2] == g:
                clash = True
                break
        if clash:
            continue
        darts[a][2] = g
        Ad2, Bd2 = _tables_from(darts, k, I)
        v = _unreached(k, N, M, Ad2, Bd2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            Ad, Bd = Ad2, Bd2
        else:
            darts[a][2] = old
    if cur == 0:
        return [tuple(x) for x in darts]
    return None


def _lift_edges(k, N, M, darts):
    """Edges of the lift: A(i, x) = i*N + x, B(j, y) = k*N + j*N + y."""
    base_B = k * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, base_B + j * N + M[x][g]))
    return 2 * k * N, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    if d < 2 or D < 2:
        return best

    Moore = lib._moore_bound(d, D)
    ks = [1, 2, 3, 4]
    kw = [0.15, 0.35, 0.30, 0.20]

    while time.monotonic() < deadline:
        k = rng.choices(ks, weights=kw)[0]
        lo = max(d, best_n // (2 * k) + 1)
        hi = Moore // (2 * k)
        if lo > hi:
            # Stop if no base size can beat the current best.
            if all(max(d, best_n // (2 * kk) + 1) > Moore // (2 * kk) for kk in ks):
                break
            continue

        # Bias toward smaller orders, which are easier to hit.
        N = lo + int((hi - lo + 1) * rng.random() ** 2)
        if N > hi:
            N = hi

        groups = _groups(N)
        rng.shuffle(groups)
        for m, kk, r in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            order, M, I = _tables(m, kk, r)
            try_deadline = min(deadline, time.monotonic() + PER_TRY)
            darts = _anneal(k, order, M, I, d, D, rng, ITERS, try_deadline)
            if darts is not None:
                n, e = _lift_edges(k, order, M, darts)
                consider(n, e)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
