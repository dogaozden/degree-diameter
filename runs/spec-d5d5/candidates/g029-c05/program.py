import math
import random
import time

import lib

GROUPS_PER_ATTEMPT = 6   # group structures tried per (p, N) attempt
MAX_BASE = 4             # largest base-graph side size p explored


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base bi-Cayley (voltage) search over semidirect products Z_m x|_r Z_k.
#
# Base graph: p vertices A_0..A_{p-1} and p vertices B_0..B_{p-1}. A "cell"
# (i, j) carries M[i][j] distinct group voltages g, giving edges
#     A(i, x) -- B(j, x*g)   for all x in G.
# Every A(i, .) and B(j, .) has degree sum_j M[i][j] = d, so M is a d-regular
# p x p multiplicity matrix (sum of d permutation matrices). Left
# multiplication by G is an automorphism, so distances only need to be checked
# from the 2p base vertices at the identity. p = 1 is the classic bi-Cayley
# graph; p >= 2 gives different orders (2 p N) and more freedom.
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


def _pattern(p, d, rng):
    """Random d-regular p x p multiplicity matrix as a sum of d permutation matrices."""
    M = [[0] * p for _ in range(p)]
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            M[i][perm[i]] += 1
    return M


def _adj(p, N, T, cells):
    """Adjacency lists of the lifted graph. A(i,x) = i*N + x, B(j,y) = p*N + j*N + y."""
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    base_b = p * N
    for i in range(p):
        for j in range(p):
            for g in cells[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + j * N + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _unreached(p, N, adj, D):
    """Number of (source, vertex) pairs at distance > D, over all 2p base sources at identity."""
    V = 2 * p * N
    sources = [i * N for i in range(p)] + [p * N + j * N for j in range(p)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        cnt = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(p, N, T, M, D, rng, deadline):
    """Simulated annealing over voltage sets to drive unreached pairs to zero. Returns cells or None."""
    cells = [[rng.sample(range(N), M[i][j]) if M[i][j] else [] for j in range(p)]
             for i in range(p)]
    nz = [(i, j) for i in range(p) for j in range(p) if M[i][j]]
    cur = _unreached(p, N, _adj(p, N, T, cells), D)
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        temp = 2.0 - 1.9 * ((it % 500) / 500.0)
        i, j = nz[rng.randrange(len(nz))]
        cell = cells[i][j]
        k = rng.randrange(len(cell))
        c = rng.randrange(N)
        if c in cell:
            continue
        old = cell[k]
        cell[k] = c
        cand = _unreached(p, N, _adj(p, N, T, cells), D)
        if cand <= cur or rng.random() < math.exp(-(cand - cur) / temp):
            cur = cand
        else:
            cell[k] = old
    return cells


def _attempt(p, N, d, D, rng, deadline):
    """Try several group structures of order N with base size p. Return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        M = _pattern(p, d, rng)
        cells = _anneal(p, N, T, M, D, rng, deadline)
        if cells is not None:
            edges = []
            base_b = p * N
            for i in range(p):
                for j in range(p):
                    for g in cells[i][j]:
                        for x in range(N):
                            edges.append((i * N + x, base_b + j * N + T[x][g]))
            return 2 * p * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_end = start + max(0.0, min(0.8 * time_limit, time_limit - 4.0))
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
            return True
        return False

    if D == 1:
        consider(2, [(0, 1)])
        return best

    if D == 2:
        consider(*lib.haar_graph(d, range(d)))

    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except Exception:
                pass

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    # Bisection over achievable orders 2*p*N, between the best known order
    # (lo, known achievable) and an upper bound (hi, not yet reached).
    if d >= 3 and D >= 2:
        pmax = min(d, MAX_BASE)
        top = lib._moore_bound(d, D) + 1
        lo, hi = best_n, top
        budget = 3.0
        while time.monotonic() < search_end:
            if hi - lo <= 2:
                hi = top
                budget = min(15.0, budget * 1.3)
                if hi - lo <= 2:
                    break
            mid = (lo + hi) // 2
            o = mid
            choice = None
            while o < hi:
                ps = [p for p in range(1, pmax + 1)
                      if o % (2 * p) == 0 and o // (2 * p) >= d]
                if ps:
                    choice = (o, ps)
                    break
                o += 1
            if choice is None:
                hi = mid
                continue
            o, ps = choice
            p = rng.choice(ps)
            N = o // (2 * p)
            att = min(search_end, time.monotonic() + budget)
            res = _attempt(p, N, d, D, rng, att)
            if res is not None and consider(*res):
                lo = o
            else:
                hi = o

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
