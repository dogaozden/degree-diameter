import random
import time

import lib


# Parent structure is kept. Two changes:
#  1. Arc-extension pruning: a set S of indices with at most s members on any line
#     has |S| <= floor(s*m/(q+1)) by double counting. If the resulting order cannot
#     beat the current best, that q is skipped and its search time goes to the rest.
#  2. New helper _grow: after the best graph is found, try attaching new vertices
#     (on either side) to random spare-degree vertices of the opposite side. Each
#     attempt is verified with lib.is_valid, so only valid, larger graphs are kept.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as index set, using the same ordering as lib.projective_points."""
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


def _sides(n, edges):
    """2-colour a bipartite graph by BFS; return (color list, adjacency)."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color, adj


def _grow(n, edges, d, D, rng, deadline, patience=3000):
    """Randomly attach new vertices to spare-degree vertices of the opposite side, keeping only valid graphs."""
    color, _ = _sides(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    cur_n, cur_e = n, list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < patience:
        side = rng.randrange(2)
        pool = [v for v in range(cur_n) if color[v] == 1 - side and deg[v] < d]
        if not pool:
            fails += 1
            continue
        k = min(d, len(pool))
        nb = rng.sample(pool, k)
        x = cur_n
        new_e = cur_e + [(x, y) for y in nb]
        if lib.is_valid(cur_n + 1, new_e, d, D):
            cur_n += 1
            cur_e = new_e
            color.append(side)
            deg.append(k)
            for y in nb:
                deg[y] += 1
            fails = 0
        else:
            fails += 1
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

        # Arc-extended graphs. Prune q whose counting bound cannot beat the current best.
        qs = []
        for q in range(2, d - 1):
            if not lib.is_prime_power(q) or q > 23:
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = q * q + q + 1
            if 2 * m + 2 * (s * m // (q + 1)) > best_n:
                qs.append(q)

        arc_deadline = start + 0.6 * time_limit
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        for q in qs:
            span = max(0.0, arc_deadline - time.monotonic())
            m, edges, nbr = data[q]
            s = d - q - 1
            slice_end = time.monotonic() + span * m / total
            total -= m
            init = _conic_init(q)
            S = _ils(m, nbr, s, rng, slice_end, init)
            if S:
                consider(*_arc_graph(m, edges, nbr, S))

        # Spend the remaining budget on random vertex attachment to the best graph.
        grow_deadline = start + 0.85 * time_limit
        if time.monotonic() < grow_deadline and best_n >= 3:
            gn, ge = _grow(best_n, list(best[1]), d, D, rng, grow_deadline)
            consider(gn, ge)

    return best
