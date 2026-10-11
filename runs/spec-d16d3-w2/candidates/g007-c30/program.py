import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family A: cyclic Haar graphs from difference covers (bold new family).
#
# H(m, S) has parts a_i = i and b_j = m + j, with a_i ~ b_{i+s} for s in S.
# |S| = d gives a d-regular bipartite graph on 2m vertices. Z_m acts by
# translation, and a_i <-> b_{-i} is an automorphism, so the diameter check
# only needs a BFS from a_0. With S containing 0 (WLOG by translation), the
# condition D = 3 is S - S = Z_m, so m <= d(d-1)+1 (= 241 for d = 16).
# For d = 16 the parent's record order 394 corresponds to m = 197.
# We search for the largest m by bisection, with simulated annealing on S.
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    """Number of vertices of H(m, S) not within distance D of a_0 (0 means valid for a_0)."""
    seen = bytearray(2 * m)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < m:
                for s in S:
                    v = m + (u + s) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                j = u - m
                for s in S:
                    v = (j - s) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * m - count


def _haar_anneal(m, d, D, rng, deadline, iters):
    """Anneal a connection set S of size d (containing 0) in Z_m so H(m, S) has diameter <= D."""
    if m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = _haar_cost(m, S, D)
    for it in range(iters):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            break
        T = 1.5 * (0.02 ** (it / iters))
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _haar_cost(m, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


# ----------------------------------------------------------------------------
# Family B: projective plane incidence and arc-extended PG(2, q) graphs (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 23)."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy arc-like set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_arc(m, s, pl, lp, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in pl[P] if cl[L] >= s}
        satQ = {Q for Q in lp[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in pl[R]) or any(Q in satQ for Q in lp[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(m, edges, pl, lp, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_candidate(q, s, deadline, rng):
    """Arc-extended PG(2, q) graph with spare degree s = d - q - 1, or None."""
    m, edges, pl, lp = _pg_data(q)
    now = time.monotonic()
    S0 = _greedy_arc(m, s, pl, lp, rng, 30, now + 0.3 * max(0.0, deadline - now))
    if not _loads_ok(S0, s, m, pl, lp):
        S0 = []
    S = _local_arc(m, s, pl, lp, S0, rng, deadline)
    if not S or not _loads_ok(S, s, m, pl, lp):
        return None
    return _arc_graph(m, edges, pl, lp, S)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Arc-extended projective planes (D = 3 only), a fixed share of the budget.
    if D == 3:
        arc_end = start + 0.3 * time_limit
        arc_qs = [q for q in range(min(d - 2, 23), 1, -1)
                  if lib.is_prime_power(q) and d - q - 1 >= 1][:3]
        for idx, q in enumerate(arc_qs):
            now = time.monotonic()
            if now >= arc_end:
                break
            dl = now + (arc_end - now) / (len(arc_qs) - idx)
            res = _arc_candidate(q, d - q - 1, dl, rng)
            if res is not None:
                consider(res[0], res[1])

    # Main new family: bisection over m with annealed difference-cover connection sets.
    hi = min(lib.moore_bound(d, D) // 2, 1500)
    lo = d
    while time.monotonic() < deadline and lo < hi:
        mid = (lo + hi + 1) // 2
        S = None
        for _ in range(2):
            S = _haar_anneal(mid, d, D, rng, deadline, 1500)
            if S is not None or time.monotonic() >= deadline:
                break
        if S is not None:
            lo = mid
            consider(*lib.haar_graph(mid, S))
        else:
            hi = mid - 1

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
