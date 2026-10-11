import random
import time

import lib


# Version notes:
# - Arc-extension warm start and iterated local search are kept from the parent.
# - New: a vertex-insertion phase. A new vertex on side s is joined to a set T of
#   spare vertices on the opposite side. For D = 3 the distance-2 requirement means
#   T must hit the neighbourhood of every vertex on side s. T is found by randomised
#   greedy set cover over spare vertices, and each insertion is accepted only if
#   lib.is_valid confirms the enlarged graph.


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


def _colors(n, edges):
    """Return (colour list, adjacency) for a bipartite graph; colour 0/1 per component start."""
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


def _hitting_set(n, adj, color, side, d, rng):
    """Randomised greedy: spare vertices on the opposite side whose neighbourhoods cover all of `side`.

    Returns a list T of at most d vertices, or None if the greedy cover fails.
    """
    uncovered = {a for a in range(n) if color[a] == side}
    cands = [t for t in range(n) if color[t] != side and len(adj[t]) < d]
    chosen = set()
    T = []
    while uncovered:
        if len(T) >= d:
            return None
        best, bestkey = None, None
        for t in cands:
            if t in chosen:
                continue
            gain = 0
            for a in adj[t]:
                if a in uncovered:
                    gain += 1
            if gain == 0:
                continue
            key = (gain, rng.random())
            if bestkey is None or key > bestkey:
                best, bestkey = t, key
        if best is None:
            return None
        T.append(best)
        chosen.add(best)
        uncovered.difference_update(adj[best])
    return T


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly insert a new vertex joined to a greedy hitting set; accept only if lib.is_valid passes."""
    edges = list(edges)
    while time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            if time.monotonic() >= deadline:
                break
            color, adj = _colors(n, edges)
            for _ in range(8):
                T = _hitting_set(n, adj, color, side, d, rng)
                if T is None:
                    continue
                cand = edges + [(n, t) for t in T]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    grew = True
                    break
            if grew:
                break
        if not grew:
            break
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.72 * time_limit
    final_deadline = start + 0.88 * time_limit
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
            if S:
                consider(*_arc_graph(m, edges, nbr, S))

        # Vertex-insertion phase on the best graph found so far.
        if best_n > 1:
            n2, e2 = _grow(best_n, list(best[1]), d, D, rng, final_deadline)
            consider(n2, e2)

    return best
