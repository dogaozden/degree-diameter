import math
import random
import time

import lib

# New routine: unstructured search for d-regular bipartite graphs with diameter <= D.
# A random d-regular bipartite graph on N + N vertices is repaired by edge-switch
# simulated annealing. Each switch replaces (a1,b1),(a2,b2) with (a1,b2),(a2,b1), which
# keeps degrees and bipartiteness. The cost is the number of ordered vertex pairs at
# distance > D, computed with bitmask balls. The order N grows whenever annealing succeeds.


def _random_biregular(N, d, rng):
    """Union of d random perfect matchings between the two sides (no repeated pairs)."""
    E = []
    used = set()
    for _ in range(d):
        ok = False
        for _try in range(3000):
            perm = list(range(N))
            rng.shuffle(perm)
            if all((a, perm[a]) not in used for a in range(N)):
                ok = True
                break
        if not ok:
            return None
        for a in range(N):
            used.add((a, perm[a]))
            E.append((a, perm[a]))
    return E


def _build_nb(N, E):
    """Adjacency lists on 2N vertices: A-vertex a is a, B-vertex b is N + b."""
    nb = [[] for _ in range(2 * N)]
    for a, b in E:
        nb[a].append(N + b)
        nb[N + b].append(a)
    return nb


def _set_edge(E, nb, N, i, a, b):
    """Re-point edge index i to (a, b), keeping adjacency lists consistent."""
    oa, ob = E[i]
    nb[oa].remove(N + ob)
    nb[N + ob].remove(oa)
    nb[a].append(N + b)
    nb[N + b].append(a)
    E[i] = (a, b)


def _unreached(nb, M, D):
    """Number of ordered vertex pairs at distance > D (zero means diameter <= D)."""
    ball = [1 << v for v in range(M)]
    for _ in range(D):
        new = []
        for v in range(M):
            x = ball[v]
            for u in nb[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(M - x.bit_count() for x in ball)


def _anneal(N, d, D, rng, deadline):
    """Edge-switch annealing on a random d-regular bipartite graph with N vertices per side."""
    E = _random_biregular(N, d, rng)
    if E is None:
        return None
    E = list(E)
    M = 2 * N
    nb = _build_nb(N, E)
    cost = _unreached(nb, M, D)
    if cost == 0:
        return E
    m = len(E)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 2.0, 0.05
    frac = 0.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - start) / span)
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (N + b2) in nb[a1] or (N + b1) in nb[a2]:
            continue
        _set_edge(E, nb, N, i, a1, b2)
        _set_edge(E, nb, N, j, a2, b1)
        c2 = _unreached(nb, M, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _set_edge(E, nb, N, i, a1, b1)
            _set_edge(E, nb, N, j, a2, b2)
    return E if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # cycle C_{2D}: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # K_{d,d}: bipartite, degree d, diameter 2. Valid fallback for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best_n and lib.is_valid(n, e, d, D):
            return n, e

    # Main search: grow the per-side order N while annealing succeeds.
    N = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline:
        if 2 * N > moore:
            break
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.2:
            break
        slice_len = max(1.0, 0.35 * remaining)
        E = _anneal(N, d, D, rng, min(deadline, now + slice_len))
        if E is not None:
            n = 2 * N
            edges = [(a, N + b) for a, b in E]
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges
                N += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
