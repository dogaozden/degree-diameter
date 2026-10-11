import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane data and arc sets.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, index, point_lines, line_points) for PG(2, q); points and lines share indices 0..m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, index, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """True if each line holds <= s points of S and each point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


# ----------------------------------------------------------------------------
# Arc-extended incidence graph with deletion repair.
#
# Vertices: points 0..m-1, lines m..2m-1, A-vertex per S-point (adjacent to its
# lines, on the point side), B-vertex per S-line (adjacent to its points, on the
# line side). A set of PG incidences (point, line) may be deleted to free degree
# for extra S elements. Bipartiteness holds by construction.
# ----------------------------------------------------------------------------

def _graph(m, point_lines, line_points, S, deleted):
    """Build (n, edges) from the S set and the set of deleted PG incidences (p, L)."""
    K = len(S)
    n = 2 * m + 2 * K
    E = []
    for p in range(m):
        for L in point_lines[p]:
            if (p, L) not in deleted:
                E.append((p, m + L))
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
        b = 2 * m + K + t
        for Q in line_points[P]:
            E.append((Q, b))
    return n, E


def _score(n, E, d, D):
    """Cost = 20 * total degree excess + number of bad pairs; returns (cost, degrees)."""
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    excess = sum(x - d for x in deg if x > d)
    bp = lib.bad_pairs(n, E, D)
    return 20 * excess + bp, deg


def _search(m, point_lines, line_points, d, D, S0, K, deadline, rng):
    """Annealing over S (size K) and deleted incidences; returns (S, n, E) with zero cost, or None."""
    S = list(S0)
    inS = set(S)
    while len(S) < K:
        p = rng.randrange(m)
        if p not in inS:
            S.append(p)
            inS.add(p)
    dele = frozenset()
    n, E = _graph(m, point_lines, line_points, S, dele)
    cost, deg = _score(n, E, d, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        if cost == 0:
            return S, n, E
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 1.5 * max(0.0, 1.0 - (now - t0) / span) + 0.05

        over = [v for v, x in enumerate(deg) if x > d]
        r = rng.random()
        newS, newDel = S, dele
        if over and r < 0.7:
            v = rng.choice(over)
            if v < m:
                cands = [(v, L) for L in point_lines[v] if (v, L) not in dele]
            elif v < 2 * m:
                L = v - m
                cands = [(p, L) for p in line_points[L] if (p, L) not in dele]
            else:
                cands = []
            if not cands:
                continue
            newDel = dele | {rng.choice(cands)}
        elif r < 0.85 and dele:
            newDel = dele - {rng.choice(tuple(dele))}
        else:
            idx = rng.randrange(K)
            p = rng.randrange(m)
            if p in inS:
                continue
            newS = S[:]
            newS[idx] = p

        n2, E2 = _graph(m, point_lines, line_points, newS, newDel)
        c2, deg2 = _score(n2, E2, d, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, dele, cost, deg, n, E = newS, newDel, c2, deg2, n2, E2
            inS = set(S)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        # Even cycle C_{2D} has diameter D.
        consider(*lib.haar_graph(D, [0, 1]))

    if D >= 3:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
            s = d - q - 1
            if s >= 1:
                m, index, point_lines, line_points = _pg_data(q)
                F = lib.GF(q)
                conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
                if q % 2 == 0:
                    conic.append(index[(0, 1, 0)])
                if _loads_ok(conic, s, m, point_lines, line_points):
                    S = conic
                else:
                    S = _greedy_arc(m, s, point_lines, line_points, rng, 30,
                                    start + 0.1 * time_limit)
                if S:
                    n3, e3 = _graph(m, point_lines, line_points, S, frozenset())
                    consider(n3, e3)
                    K = len(S) + 1
                    # Grow the arc one element at a time, repairing by edge deletion.
                    while time.monotonic() < deadline:
                        now = time.monotonic()
                        res = _search(m, point_lines, line_points, d, D, S, K,
                                      now + 0.5 * (deadline - now), rng)
                        if res is None:
                            break
                        S, n3, e3 = res
                        consider(n3, e3)
                        K += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
