import random
import time

import lib


# Combined program: PG(2,q) incidence base, arc-extension with a conic or
# iterated-local-search arc, then randomized cover growth. Every candidate is
# checked with lib.is_valid before it is kept.
#
# Growth rule: a new vertex v on one side, joined to chosen vertices s_1..s_k on
# the other side, keeps diameter <= D when the radius-(D-1) balls of the s_i
# cover all vertices. Adding vertices and keeping old edges never increases
# distances, so each accepted step preserves validity.


def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] lists the indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic(q):
    """Conic (plus nucleus for even q) as an index set: an arc, or a hyperoval for even q."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, s, nbr, m):
    """True if every index X has at most s members of S in its neighbourhood nbr[X]."""
    cnt = [0] * m
    for P in S:
        for X in nbr[P]:
            cnt[X] += 1
    return max(cnt, default=0) <= s


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
            if pending or (len(removed) > 1 and rng.random() >= 0.01):
                for Y in reversed(removed):  # roll back exactly
                    add(Y)
                continue
            add(v)
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


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidates (balls as bitmasks); None if it fails."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        bg = max(gains)
        if bg <= 0:
            break
        if randomize:
            thr = bg - (1 if rng.random() < 0.3 else 0)
            opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
            i = rng.choice(opts)
        else:
            i = gains.index(bg)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex whose neighbourhood covers all vertices within D-1 of it; returns (n, edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        order = [0, 1]
        rng.shuffle(order)
        for c in order:
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = _cover(cands, ball, full, d, rng, False)
            attempt = 0
            while chosen is None and attempt < 40 and time.monotonic() < deadline:
                attempt += 1
                chosen = _cover(cands, ball, full, d, rng, True)
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                added = True
                break
        if not added:
            break
    return n, edges


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

    if D >= 3:
        bases = []
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            pn, pe = lib.projective_plane_incidence(pg_qs[0])
            consider(pn, pe)
            bases.append((pn, pe))

        # Arc-extended graphs: S is a set where every index has <= s = d-q-1 members in its neighbourhood.
        arc_deadline = start + 0.35 * time_limit
        qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        for q in qs:
            m, edges, nbr = data[q]
            s = d - q - 1
            if s < 1:
                continue
            cs = _conic(q)
            if not _loads_ok(cs, s, nbr, m):
                cs = []
            if s == 2 and cs:
                S = cs  # conic / hyperoval is already maximal for this constraint
            else:
                span = max(0.0, arc_deadline - time.monotonic())
                slice_end = time.monotonic() + span * m / total
                S = _ils(m, nbr, s, rng, slice_end, cs)
                if len(cs) > len(S):
                    S = cs
            if S and _loads_ok(S, s, nbr, m):
                g = _arc_graph(m, edges, nbr, S)
                consider(*g)
                bases.append(g)

        # Cover-based growth on the largest bases, with the remaining time shared.
        bases.sort(key=lambda c: -c[0])
        for idx, (n0, e0) in enumerate(bases[:2]):
            now = time.monotonic()
            slice_end = now + max(0.0, deadline - now) / (2 - idx)
            n2, e2 = _grow(n0, e0, d, D, slice_end, random.Random(seed * 31 + idx))
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
