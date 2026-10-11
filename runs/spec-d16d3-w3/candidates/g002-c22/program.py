import random
import time

import lib


# Bold variant. Phase 1 builds the arc-extended PG(2,q) graph by iterated local
# search (ILS), as in the parent. Phase 2 is a different move: it treats the
# finished graph as a base and tries to attach new vertices one at a time to
# spare-degree vertices on the opposite side. A candidate is kept only if the
# whole graph still passes lib.bad_pairs == 0 and lib.is_valid. Every accepted
# state is valid, so the fallback chain always returns a valid graph.
# The attachment search is a randomized heuristic and may add nothing; the
# returned graph is never worse than the phase-1 result.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as an index set, using the ordering of lib.projective_points."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _ils(m, nbr, s, rng, deadline, init):
    """Iterated local search for a large S with every X having at most s members of S in nbr[X]."""
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
            if len(removed) <= 1 or rng.random() < 0.01:
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


def _sides_and_degrees(n, E):
    """Return a 2-colouring (per vertex 0/1) of a bipartite graph and the vertex degrees."""
    adj = [[] for _ in range(n)]
    deg = [0] * n
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
        deg[u] += 1
        deg[v] += 1
    col = [-1] * n
    for s in range(n):
        if col[s] < 0:
            col[s] = 0
            stack = [s]
            while stack:
                u = stack.pop()
                for v in adj[u]:
                    if col[v] < 0:
                        col[v] = 1 - col[u]
                        stack.append(v)
    return col, deg


def _attach_search(n, E, d, D, rng, deadline, best_n):
    """Try to attach new vertices to spare-degree vertices of the opposite side.

    Accept an attachment only if the whole graph keeps bad_pairs == 0 and passes is_valid.
    Returns (n, E) for the final accepted state, or None if nothing was accepted.
    """
    cur_n, cur_E = n, E
    improved = False
    while time.monotonic() < deadline:
        col, deg = _sides_and_degrees(cur_n, cur_E)
        s = rng.randrange(2)
        cands = [u for u in range(cur_n) if col[u] != s and deg[u] < d]
        if not cands:
            s = 1 - s
            cands = [u for u in range(cur_n) if col[u] != s and deg[u] < d]
            if not cands:
                break
        rng.shuffle(cands)
        nb = cands[:min(d, len(cands))]
        E2 = cur_E + [(u, cur_n) for u in nb]
        n2 = cur_n + 1
        if lib.bad_pairs(n2, E2, D) == 0 and lib.is_valid(n2, E2, d, D):
            cur_n, cur_E = n2, E2
            improved = True
    if improved and cur_n > best_n:
        return cur_n, cur_E
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    phase1_end = start + 0.6 * time_limit
    total_end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
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

        # Phase 1: arc-extended graphs, ILS time shared across q in proportion to m.
        qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        span = max(0.0, phase1_end - time.monotonic())
        for q in qs:
            m, edges, nbr = data[q]
            s = d - q - 1
            if s < 1:
                continue
            slice_end = time.monotonic() + span * m / total
            init = _conic_init(q)
            S = _ils(m, nbr, s, rng, slice_end, init)
            if S:
                consider(*_arc_graph(m, edges, nbr, S))

        # Phase 2: attach extra vertices to the best graph found so far.
        grown = _attach_search(best_n, list(best[1]) if best_n > 0 else [],
                               d, D, rng, total_end, best_n)
        if grown is not None:
            consider(*grown)

    return best
