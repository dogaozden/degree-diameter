import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search for bipartite lifts over non-abelian groups.
#
# New construction (multi-orbit voltage lift):
#   Base graph: p "A" vertices and p "B" vertices. The multiplicity matrix M
#   (p x p, nonnegative integers, all row and column sums equal to d) says how
#   many parallel darts join A_i to B_j. Each dart carries a voltage g in a
#   group G of order N. The lift has vertices A_{i,x} and B_{j,y} for x, y in G,
#   and edges A_{i,x} -- B_{j, x*g} for every dart (i, j, g).
#   Left multiplication by h is an automorphism, so each fibre is one orbit and
#   the diameter can be checked from the p + p fibre representatives A_{i,e}, B_{j,e}.
#   Total order 2*p*N, degree d, bipartite by construction.
#
# Distinct voltages are required for darts that share the same (i, j) pair,
# which keeps the lift simple. The base multiplicity matrix is drawn as a sum of
# d random permutation matrices, so row and column sums are exactly d.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 3000
GROUPS_PER_ITEM = 6
ITEM_BUDGET = 2.0


def _baseline_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _random_matrix(p, d, rng):
    """p x p nonnegative integer matrix whose rows and columns each sum to d."""
    M = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            M[i][perm[i]] += 1
    return M


def _cost(N, p, T, invs, darts, D):
    """Total number of (fibre representative, vertex) pairs not within distance D."""
    a_nb = [[] for _ in range(p)]
    b_nb = [[] for _ in range(p)]
    for i, j, g in darts:
        a_nb[i].append((j, g))
        b_nb[j].append((i, invs[g]))
    pn = p * N
    V = 2 * pn
    total = 0
    for s in range(2 * p):
        src = s * N
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < pn:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in a_nb[i]:
                        v = pn + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - pn, N)
                    row = T[y]
                    for i, h in b_nb[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, p, T, invs, darts, D, rng, deadline):
    """Simulated annealing over voltages until the lift has diameter <= D."""
    cur = _cost(N, p, T, invs, darts, D)
    for it in range(ANNEAL_ITERS):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        t = rng.randrange(len(darts))
        i, j, g_old = darts[t]
        c = rng.randrange(N)
        if any(a == i and b == j and g == c for a, b, g in darts):
            continue
        darts[t] = [i, j, c]
        new = _cost(N, p, T, invs, darts, D)
        temp = max(0.05, 2.0 * (1.0 - it / ANNEAL_ITERS))
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            darts[t] = [i, j, g_old]
    return darts if cur == 0 else None


def _try_item(N, p, d, D, rng, deadline):
    """Try several groups and multiplicity matrices of order N; return (T, darts) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    tries = 0
    for m, k, r in groups:
        if time.monotonic() > deadline or tries >= GROUPS_PER_ITEM:
            break
        tries += 1
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_matrix(p, d, rng)
        if max(max(row) for row in M) > N:
            continue
        darts = []
        for i in range(p):
            for j in range(p):
                for g in rng.sample(range(N), M[i][j]):
                    darts.append([i, j, g])
        res = _anneal(N, p, T, invs, darts, D, rng, deadline)
        if res is not None:
            return T, res
    return None


def _edges(N, p, T, darts):
    """Edge list of the lift; vertex A_{i,x} = i*N + x, B_{j,y} = (p + j)*N + y."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (p + j) * N + T[x][g]))
    return 2 * p * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _baseline_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2 and D >= 2:
        Moore = lib._moore_bound(d, D)
        low = int(0.45 * Moore)
        items = []
        for p in (2, 1, 3):
            Nmax = Moore // (2 * p)
            lo = max(d, (low + 2 * p - 1) // (2 * p))
            for N in range(lo, Nmax + 1):
                items.append((2 * p * N, p, N))
        items.sort()

        for cnt, p, N in items:
            if time.monotonic() >= deadline:
                break
            if cnt <= best[0]:
                continue
            item_deadline = min(deadline, time.monotonic() + ITEM_BUDGET)
            res = _try_item(N, p, d, D, rng, item_deadline)
            if res is not None:
                T, darts = res
                n, e = _edges(N, p, T, darts)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
