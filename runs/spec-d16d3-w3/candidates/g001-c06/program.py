import random
import time

import lib


# Version notes: the arc-extension set S is still found by an iterated local
# search on the polarity-style incidence structure of PG(2, q), warm-started
# from a conic. New in this version: after the arc graph is built, a
# spare-degree completion step adds A-B edges between the new vertices, which
# still have free degree. Adding edges never increases any distance, so
# diameter is preserved, and bipartiteness holds because A sits on the point
# side and B on the line side. This does not add vertices, but it makes the
# graph's degree profile tighter and gives any later extension more room.
# Every candidate is still checked with lib.is_valid before it is accepted.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as an index set, using lib.projective_points ordering."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _ils(m, nbr, s, rng, deadline, init):
    """Iterated local search for a large S with every X having <= s members of S in nbr[X]."""
    nbs = [set(x) for x in nbr]
    inS = [False] * m
    cnt = [0] * m
    members = set()

    def add(v):
        inS[v] = True
        members.add(v)
        for X in nbr[v]:
            cnt[X] += 1

    def remove(v):
        inS[v] = False
        members.discard(v)
        for X in nbr[v]:
            cnt[X] -= 1

    for v in init:
        if not inS[v] and all(cnt[X] < s for X in nbr[v]):
            add(v)
    best = list(members)

    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        v = rng.randrange(m)
        if inS[v]:
            continue
        full = [X for X in nbr[v] if cnt[X] >= s]
        if not full:
            add(v)
        else:
            removed = []
            pending = full
            while pending:
                X = pending[rng.randrange(len(pending))]
                cands = [Y for Y in nbr[X] if inS[Y]]
                if not cands:
                    break
                rng.shuffle(cands)
                bestY, bestc = cands[0], -1
                for Y in cands:
                    c = 0
                    for Z in pending:
                        if Z in nbs[Y]:
                            c += 1
                    if c > bestc:
                        bestY, bestc = Y, c
                remove(bestY)
                removed.append(bestY)
                pending = [Z for Z in pending if cnt[Z] >= s]
            if not pending and (len(removed) <= 1 or rng.random() < 0.01):
                add(v)
            else:
                for Y in reversed(removed):
                    add(Y)
                continue
        if len(members) > len(best):
            best = list(members)
    return best


def _arc_graph(m, edges, nbr, S):
    """PG(2,q) incidence plus an A-vertex per element of S (joined to its lines) and a B-vertex (joined to its points)."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in nbr[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in nbr[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _spare_completion(n, edges, m, k, d, rng):
    """New helper: greedily add A-B edges between the arc vertices while degrees stay <= d.

    A-vertices are 2m..2m+k-1 (point side); B-vertices are 2m+k..2m+2k-1 (line side),
    so every added edge joins opposite sides and bipartiteness is kept. Adding edges
    only shortens paths, so the diameter bound still holds.
    """
    deg = [0] * n
    seen = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        seen.add((u, v) if u < v else (v, u))
    A = list(range(2 * m, 2 * m + k))
    B = list(range(2 * m + k, 2 * m + 2 * k))
    pairs = [(a, b) for a in A for b in B]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            key = (a, b) if a < b else (b, a)
            if key not in seen:
                seen.add(key)
                deg[a] += 1
                deg[b] += 1
                out.append((a, b))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
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

    if D >= 3:
        # Plain projective plane for the largest prime power q with q + 1 <= d.
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            consider(*lib.projective_plane_incidence(pg_qs[0]))

        # Arc-extended graphs, with ILS time shared across q in proportion to m.
        qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        span = max(0.0, deadline - time.monotonic())
        for q in qs:
            m, edges, nbr = data[q]
            s = d - q - 1
            if s < 1:
                continue
            slice_end = time.monotonic() + span * m / total
            init = _conic_init(q)
            S = _ils(m, nbr, s, rng, slice_end, init)
            if not S:
                continue
            n, E = _arc_graph(m, edges, nbr, S)
            consider(n, E)
            # New step: spend the spare degree on A-B edges (vertex count unchanged).
            E2 = _spare_completion(n, E, m, len(S), d, rng)
            consider(n, E2)

    return best
