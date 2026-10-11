"""d16D3 search program: PG(2,q) base, conic arc extension, then annealed vertex insertion.

Constructions, in order:
  1. K_{d,d} as a safe fallback (valid for D >= 2).
  2. Incidence graphs of PG(2,q) for every prime power q <= d-1 (diameter 3).
  3. For each q with spare degree s = d-q-1 >= 2, a conic (plus nucleus for even q)
     arc of points and lines, with a new A and a new B vertex per arc element.
     Diameter stays 3 and degrees stay <= d (verified with the load check).
  4. For D == 3 only: grow the best base graph by inserting one (A, B) pair at a time.
     Each insertion is repaired by annealing over edge switches and spare-degree
     edge additions, minimising the count of vertex pairs at distance > 3.
     A failed attempt is rolled back to the last committed graph.

Every returned graph is checked with lib.is_valid, and the fallback is kept if a check fails.
"""
import math
import random
import time

import lib


def _prime_powers_desc(limit):
    return [q for q in range(limit, 1, -1) if lib.is_prime_power(q)]


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line meets <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _pg_candidates(d, deadline):
    """Yield (n, edges, side) for PG(2,q) incidence and its conic-extended versions."""
    out = []
    for q in _prime_powers_desc(d - 1):
        if time.monotonic() > deadline:
            break
        m2, edges = lib.projective_plane_incidence(q)
        m = m2 // 2
        out.append((m2, edges, [0] * m + [1] * m))
        s = d - q - 1
        if s < 2:
            continue
        F = lib.GF(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        # Conic (tangent-line dual with the same vectors), plus nucleus for even q.
        S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            S.append(index[(0, 1, 0)])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        k = len(S)
        n = 2 * m + 2 * k
        E = list(edges)
        for t, P in enumerate(S):
            for L in point_lines[P]:
                E.append((2 * m + t, m + L))       # new A vertex on the point side
        for t, P in enumerate(S):
            for Q in line_points[P]:
                E.append((Q, 2 * m + k + t))       # new B vertex on the line side
        out.append((n, E, [0] * m + [1] * m + [0] * k + [1] * k))
    return out


def _nbr_from(n, E):
    nbr = [set() for _ in range(n)]
    for a, b in E:
        nbr[a].add(b)
        nbr[b].add(a)
    return nbr


def _cost(n, nbr):
    """Number of unordered vertex pairs at distance > 3 (unreachable pairs included)."""
    r1 = [0] * n
    for v in range(n):
        x = 1 << v
        for u in nbr[v]:
            x |= 1 << u
        r1[v] = x
    r2 = [0] * n
    for v in range(n):
        x = r1[v]
        for u in nbr[v]:
            x |= r1[u]
        r2[v] = x
    total = 0
    for v in range(n):
        x = r2[v]
        for u in nbr[v]:
            x |= r2[u]
        total += n - x.bit_count()
    return total // 2


def _anneal(n, nbr, E, A, B, d, deadline, rng):
    """Repair the graph until every pair is within distance 3. E entries are (side0, side1).

    Moves:
      - edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps all degrees,
      - add an edge between two vertices with spare degree (never raises the cost).
    Returns True if cost 0 is reached before the deadline.
    """
    cost = _cost(n, nbr)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 1.0 * (0.03 ** frac)
        if rng.random() < 0.5 and len(E) >= 2:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or b2 in nbr[a1] or b1 in nbr[a2]:
                continue
            nbr[a1].discard(b1); nbr[b1].discard(a1)
            nbr[a2].discard(b2); nbr[b2].discard(a2)
            nbr[a1].add(b2); nbr[b2].add(a1)
            nbr[a2].add(b1); nbr[b1].add(a2)
            c2 = _cost(n, nbr)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                E[i] = (a1, b2)
                E[j] = (a2, b1)
                cost = c2
                if cost == 0:
                    return True
            else:
                nbr[a1].discard(b2); nbr[b2].discard(a1)
                nbr[a2].discard(b1); nbr[b1].discard(a2)
                nbr[a1].add(b1); nbr[b1].add(a1)
                nbr[a2].add(b2); nbr[b2].add(a2)
        else:
            defA = [a for a in A if len(nbr[a]) < d]
            defB = [b for b in B if len(nbr[b]) < d]
            if not defA or not defB:
                continue
            a = rng.choice(defA)
            b = rng.choice(defB)
            if b in nbr[a]:
                continue
            nbr[a].add(b)
            nbr[b].add(a)
            E.append((a, b))
            cost = _cost(n, nbr)  # adding an edge never increases the cost
            if cost == 0:
                return True
    return cost == 0


def _grow(n, side, E, d, D, deadline, rng):
    """Insert (A, B) pairs one at a time, each followed by annealed repair.

    Returns the last committed (n, edges) state, which is always repaired to cost 0.
    """
    bound = 2 * sum((d - 1) ** i for i in range(D))  # Moore bound for bipartite graphs
    fails = 0
    while fails < 3 and time.monotonic() < deadline and n + 2 <= bound:
        cn = n + 2
        cE = list(E)
        cside = side + [0, 1]
        a, b = n, n + 1
        cE.append((a, b))
        nbr = _nbr_from(cn, cE)
        A = [v for v in range(cn) if cside[v] == 0]
        B = [v for v in range(cn) if cside[v] == 1]
        candB = [v for v in B if v != b and len(nbr[v]) < d]
        rng.shuffle(candB)
        for v in candB[:d - 1]:
            nbr[a].add(v); nbr[v].add(a); cE.append((a, v))
        candA = [v for v in A if v != a and len(nbr[v]) < d]
        rng.shuffle(candA)
        for v in candA[:d - 1]:
            nbr[b].add(v); nbr[v].add(b); cE.append((v, b))
        remaining = deadline - time.monotonic()
        chunk_end = min(deadline, time.monotonic() + max(2.0, remaining / 3.0))
        if _anneal(cn, nbr, cE, A, B, d, chunk_end, rng):
            n, E, side = cn, cE, cside
            fails = 0
        else:
            fails += 1
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_side = [0] * d + [1] * d
    if D == 2:
        return best_n, best_e

    # D >= 3: projective-plane bases and conic-extended bases (diameter 3).
    for n_c, e_c, s_c in _pg_candidates(d, start + 0.3 * time_limit):
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best_n, best_e, best_side = n_c, e_c, s_c

    # Growth by annealed insertion, only for D == 3.
    if D == 3 and time.monotonic() < deadline:
        n2, e2 = _grow(best_n, best_side, list(best_e), d, D, deadline, rng)
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
