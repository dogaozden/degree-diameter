import itertools
import random
import time

import lib


def _gq_incidence(q, d, rng):
    """Incidence graph of the symplectic generalized quadrangle W(q) (order 2(q+1)(q^2+1), degree q+1),
    then extended with extra point-line edges to fill degree up to d. Diameter 4, bipartite."""
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    neg = [0] * q
    inv = [0] * q
    for a in range(q):
        for b in range(q):
            if A[a][b] == 0:
                neg[a] = b
            if M[a][b] == 1:
                inv[a] = b

    def norm(v):
        # Normalise a nonzero vector so its first nonzero coordinate is 1.
        for x in v:
            if x:
                s = inv[x]
                return tuple(M[s][y] for y in v)
        return None

    # Points of PG(3, q).
    pts = []
    idx = {}
    for v in itertools.product(range(q), repeat=4):
        if any(v) and norm(v) == v:
            idx[v] = len(pts)
            pts.append(v)
    NP = len(pts)

    def sym(x, y):
        # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2 over GF(q).
        t1 = A[M[x[0]][y[1]]][neg[M[x[1]][y[0]]]]
        t2 = A[M[x[2]][y[3]]][neg[M[x[3]][y[2]]]]
        return A[t1][t2]

    # Totally isotropic lines: span of perpendicular pairs {P, Q}.
    lines = set()
    for i, P in enumerate(pts):
        for j, Q in enumerate(pts):
            if j == i or sym(P, Q) != 0:
                continue
            L = {i}
            for t in range(q):
                w = tuple(A[Q[k]][M[t][P[k]]] for k in range(4))
                L.add(idx[norm(w)])
            lines.add(frozenset(L))
    lines = sorted(tuple(sorted(L)) for L in lines)
    if len(lines) != (q + 1) * (q * q + 1):
        raise ValueError("unexpected number of lines")
    NL = len(lines)

    edges = []
    E = set()
    for k, L in enumerate(lines):
        for i in L:
            E.add((i, NP + k))
            edges.append((i, NP + k))
    deg = [0] * (NP + NL)
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    # Use the spare degree (d - (q+1)) with extra point-line edges.
    # Extra edges keep the graph bipartite and cannot increase distances.
    spare = d - (q + 1)
    for _ in range(spare):
        order = list(range(NP))
        rng.shuffle(order)
        for p in order:
            if deg[p] >= d:
                continue
            cands = [NP + k for k in range(NL)
                     if deg[NP + k] < d and (p, NP + k) not in E]
            if not cands:
                continue
            l = rng.choice(cands)
            E.add((p, l))
            edges.append((p, l))
            deg[p] += 1
            deg[l] += 1
    return NP + NL, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    # D = 3 with d-1 a prime power: projective plane incidence meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Bold route for D >= 4: generalized quadrangle incidence graph, largest usable q first.
    if D >= 4:
        for q in range(min(d - 1, 11), 1, -1):
            if time.monotonic() > start + 0.5 * time_limit:
                break
            if not lib.is_prime_power(q):
                continue
            try:
                n, edges = _gq_incidence(q, d, rng)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                continue

    # Safe fallback: the parent's Haar-graph search.
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
