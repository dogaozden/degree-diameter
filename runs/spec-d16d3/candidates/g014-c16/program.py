import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases (diameter 3) and arc extensions.
# ----------------------------------------------------------------------------

def _pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_lines(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); point i and line i share index i."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _arc_search(m, s, point_lines, line_points, rng, deadline):
    """Local search for a point set S with every line holding <= s points of S and every point on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    best = []
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
        else:
            satL = {L for L in point_lines[P] if cl[L] >= s}
            satQ = {Q for Q in line_points[P] if cp[Q] >= s}
            B = [R for R in S
                 if any(L in satL for L in point_lines[R])
                 or any(Q in satQ for Q in line_points[R])]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
                for R in B:
                    remove(R)
                if fits(P):
                    add(P)
                else:
                    for R in B:
                        add(R)
                    continue
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus an A-vertex per S-point (joined to its lines) and a B-vertex per S-point (joined to its points)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, P in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[P]:
            E.append((Q, b))
    return n, E


def _arc_phase(d, rng, deadline, consider):
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    qs.sort(reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp = _pg_lines(q)
        S = _arc_search(m, d - q - 1, pl, lp, rng, now + share)
        if S:
            consider(*_arc_graph(m, edges, pl, lp, S))


# ----------------------------------------------------------------------------
# New family for D = 3: Haar-type bi-Cayley graphs over groups of order N.
#
# Vertices A_g = g and B_h = N + h. Edges (g, N + g*s) for s in S, |S| = d.
# A-A distance <= 2 needs S S^{-1} = G; B-B distance <= 2 needs S^{-1} S = G.
# Then every pair is within distance 3, and the graph is d-regular bipartite
# on 2N vertices. Search for S with both covers complete.
# ----------------------------------------------------------------------------

def _group_for(N, rng):
    """Random group of order N as a semidirect product Z_m x| Z_k (cyclic if no valid r found)."""
    if rng.random() < 0.3:
        return lib.semidirect_group(N, 1, 1)
    ks = [k for k in range(2, 13) if N % k == 0 and N // k >= 2]
    rng.shuffle(ks)
    for k in ks[:3]:
        m = N // k
        for _ in range(80):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return lib.semidirect_group(m, k, r)
    return lib.semidirect_group(N, 1, 1)


def _cover_search(d, N, MT, INV, rng, deadline):
    """Simulated annealing for S (|S| = d) with S S^{-1} = G and S^{-1} S = G; returns S or None."""

    def cost(S):
        c1 = [0] * N
        c2 = [0] * N
        for s in S:
            row = MT[s]
            irow = MT[INV[s]]
            for t in S:
                c1[row[INV[t]]] += 1
                c2[irow[t]] += 1
        return c1.count(0) + c2.count(0)

    S = rng.sample(range(N), d)
    c = cost(S)
    T = 1.0
    it = 0
    while c > 0:
        it += 1
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        if it % 4000 == 0:
            T = 1.0
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = cost(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.2, T * 0.999)
    return list(S) if c == 0 else None


def _haar_phase(d, rng, deadline, consider, best_n):
    """Sweep group orders N upward from the current record half-order."""
    N = best_n // 2 + 1
    Nmax = min(d * (d - 1) + 1, 300)
    fails = 0
    while N <= Nmax and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(0.8, min(4.0, remaining / 6)))
        order, mul, inv = _group_for(N, rng)
        MT = [[mul(x, y) for y in range(N)] for x in range(N)]
        INV = [inv(x) for x in range(N)]
        S = _cover_search(d, N, MT, INV, rng, slice_end)
        if S is not None:
            e = [(g, N + MT[g][s]) for g in range(N) for s in S]
            consider(2 * N, e)
            N += 1
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                N += 1
                fails = 0


# ----------------------------------------------------------------------------
# Cyclic Haar hill-climb for D >= 4 (secondary).
# ----------------------------------------------------------------------------

def _cyclic_search(d, D, rng, deadline, consider, best_n):
    N = max(d + 1, best_n // 2 + 1)
    while time.monotonic() < deadline and N - 1 >= d:
        S = [0] + rng.sample(range(1, N), d - 1)
        n, e = lib.haar_graph(N, S)
        c = lib.bad_pairs(n, e, D)
        for _ in range(150):
            if c == 0 or time.monotonic() >= deadline:
                break
            cand = [x for x in range(1, N) if x not in S]
            if not cand:
                break
            T = S[:]
            T[rng.randrange(1, d)] = rng.choice(cand)
            n2, e2 = lib.haar_graph(N, T)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= c:
                S, c = T, c2
        if c == 0:
            n, e = lib.haar_graph(N, S)
            consider(n, e)
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = [n0, e0]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    if D >= 3:
        q = _pg_q(d)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))

    if D == 3:
        _arc_phase(d, rng, start + 0.3 * budget, consider)
        _haar_phase(d, rng, deadline, consider, best[0])
    elif D >= 4 and d >= 2:
        _cyclic_search(d, D, rng, deadline, consider, best[0])

    if not lib.is_valid(best[0], best[1], d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return n0, e0
    return best[0], best[1]
