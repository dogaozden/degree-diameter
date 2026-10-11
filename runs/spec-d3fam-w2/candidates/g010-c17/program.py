import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (safe fallbacks): record Araujo-Pardo/Lopez graph for d = q + 2,
# projective plane incidence graphs, and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-base voltage lifts over small (non-abelian) groups.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}. For each
# base index i and offset t, A_i is joined to B_{(i+t) mod k} by m_t darts,
# where sum_t m_t = d. Each dart carries a group voltage g; the lift has
# vertices (A_i, x) and (B_j, y) for x, y in G (|G| = N), with edges
# (A_i, x) -- (B_j, x*g). Darts sharing the same (i, t) get distinct voltages,
# so the lift is simple and d-regular, and it is bipartite by construction.
#
# Left multiplication by G is an automorphism of the lift, so diameter <= D
# holds iff every base vertex's ball of radius D (around its identity lift)
# covers the whole graph. The cost is the number of uncovered (source, vertex)
# pairs over the 2k base sources, which needs only 2k BFS runs per evaluation.
# Voltages are optimised by simulated annealing. The order 2kN can be
# larger than the bi-Cayley family (k = 1), which is the original approach.
# Every candidate is verified with lib.is_valid before it is returned.
# ----------------------------------------------------------------------------

def _group_specs(N, rng, cap=10):
    """Cyclic group plus a random sample of semidirect products Z_a x| Z_k of order N."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    """Multiplication table M[x][y] = x*y and inverse table I[x] for the group named by spec."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return M, I


def _cost(darts, N, k, M, I, D):
    """Number of uncovered (base source, vertex) pairs at distance > D from the source."""
    Aadj = [[] for _ in range(k)]
    Badj = [[] for _ in range(k)]
    for i, j, g, _ in darts:
        Aadj[i].append((j, g))
        Badj[j].append((i, g))
    kN = k * N
    V = 2 * kN
    total = 0
    for s in range(2 * k):
        src = s * N  # identity element of block s
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < kN:
                    i, x = divmod(v, N)
                    row = M[x]
                    for j, g in Aadj[i]:
                        w = (k + j) * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    j, y = divmod(v - kN, N)
                    row = M[y]
                    for i, g in Badj[j]:
                        w = i * N + row[I[g]]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - reached
    return total


def _anneal(N, k, d, M, I, D, m, rng, deadline, moves):
    """Anneal voltages for the base pattern m (sum m = d). Returns the dart list or None."""
    if max(m) > N:
        return None
    darts = []
    for i in range(k):
        for t in range(k):
            if m[t]:
                for g in rng.sample(range(N), m[t]):
                    darts.append([i, (i + t) % k, g, (i, t)])
    c = _cost(darts, N, k, M, I, D)
    if c == 0:
        return darts
    T0 = 1.5
    for it in range(moves):
        if (it & 7) == 0 and time.monotonic() >= deadline:
            return None
        idx = rng.randrange(len(darts))
        key = darts[idx][3]
        newg = rng.randrange(N)
        if any(dd[3] == key and dd[2] == newg for dd in darts):
            continue
        old = darts[idx][2]
        darts[idx][2] = newg
        nc = _cost(darts, N, k, M, I, D)
        delta = nc - c
        T = T0 * (0.03 ** (it / moves))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = nc
            if c == 0:
                return darts
        else:
            darts[idx][2] = old
    return None


def _search_N(N, k, d, D, rng, deadline):
    """Search for a valid voltage assignment on a group of order N. Returns (darts, M) or None."""
    specs = _group_specs(N, rng)
    tabs = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in tabs:
            try:
                tabs[spec] = _tables(spec, N)
            except Exception:
                tabs[spec] = None
        tab = tabs[spec]
        if tab is None:
            continue
        M, I = tab
        m = [0] * k
        for _ in range(d):
            m[rng.randrange(k)] += 1
        darts = _anneal(N, k, d, M, I, D, m, rng, deadline, 2000)
        if darts is not None:
            return darts, M
    return None


def _edges_from(N, k, darts, M):
    """Lift edges: (A_i, x) = i*N + x joins (B_j, x*g) = (k+j)*N + M[x][g]."""
    edges = []
    for i, j, g, _ in darts:
        for x in range(N):
            edges.append((i * N + x, (k + j) * N + M[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

        # New search: multi-base voltage lifts over small groups.
        moore = lib.moore_bound(d, D)
        for k in (2, 3, 1):
            if time.monotonic() >= deadline:
                break
            N = best[0] // (2 * k) + 1
            while 2 * k * N <= moore and time.monotonic() < deadline:
                rem = deadline - time.monotonic()
                res = _search_N(N, k, d, D, rng, time.monotonic() + 0.5 * rem)
                if res is None:
                    break
                darts, M = res
                n = 2 * k * N
                e = _edges_from(N, k, darts, M)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                N = n // (2 * k) + 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
