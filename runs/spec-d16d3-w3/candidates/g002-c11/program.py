import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extension.
#
# PG(2, q) has m = q^2+q+1 points and lines, indexed by the same vectors, with
# X ~ Y iff dot(X, Y) = 0. For a set S of indices with cnt[X] = |S ∩ nbr[X]| <= s
# for every X, where s = d - q - 1, adding an A-vertex per element of S (joined
# to its lines) and a B-vertex per element of S (joined to its points) keeps all
# degrees <= d and the diameter at 3. Points on the A side and lines on the B
# side give a bipartition.
#
# The set S is found by an iterated local search: insert a random index,
# evict only the members that block it, keep plateau (1-for-1) moves, and
# perturb or restart from the best set after a stall. The conic is the warm start.
# ----------------------------------------------------------------------------

_STALL_FACTOR = 60


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
    """Iterated local search for a large S with cnt[X] = |S ∩ nbr[X]| <= s for every X."""
    nbs = [set(x) for x in nbr]
    inS = [False] * m
    cnt = [0] * m
    mem = []
    pos = [-1] * m

    def add(v):
        inS[v] = True
        pos[v] = len(mem)
        mem.append(v)
        for X in nbr[v]:
            cnt[X] += 1

    def remove(v):
        inS[v] = False
        i = pos[v]
        last = mem[-1]
        mem[i] = last
        pos[last] = i
        mem.pop()
        pos[v] = -1
        for X in nbr[v]:
            cnt[X] -= 1

    for v in init:
        if not inS[v] and all(cnt[X] < s for X in nbr[v]):
            add(v)
    best = list(mem)

    stall = 0
    limit = _STALL_FACTOR * m
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        if stall > limit:
            stall = 0
            if rng.random() < 0.5:
                for v in list(mem):
                    remove(v)
                for v in best:
                    add(v)
            else:
                for _ in range(min(3, len(mem))):
                    remove(mem[rng.randrange(len(mem))])
            continue
        v = rng.randrange(m)
        if inS[v]:
            continue
        stall += 1
        removed = []
        while True:
            full = [X for X in nbr[v] if cnt[X] >= s]
            if not full:
                break
            X = full[rng.randrange(len(full))]
            cands = [Y for Y in nbr[X] if inS[Y]]
            rng.shuffle(cands)
            bestY, bestc = cands[0], -1
            for Y in cands:
                nY = nbs[Y]
                c = 0
                for Z in full:
                    if Z in nY:
                        c += 1
                if c > bestc:
                    bestY, bestc = Y, c
            remove(bestY)
            removed.append(bestY)
        if len(removed) <= 1 or rng.random() < 0.02:
            add(v)
            if len(mem) > len(best):
                best = list(mem)
                stall = 0
        else:
            for Y in reversed(removed):  # exact rollback
                add(Y)
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


# ----------------------------------------------------------------------------
# Cover-based vertex growth: a new vertex joined to <= d same-side vertices with
# spare degree whose radius-(D-1) balls cover the whole graph. Diameter stays <= D.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _greedy_cover(cands, ball, full, d):
    """Greedy cover of `full` by at most d candidate balls; None if it fails."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        bi = max(range(len(pool)), key=lambda i: (ball[pool[i]] & ~covered).bit_count())
        s = pool.pop(bi)
        if (ball[s] & ~covered) == 0:
            break
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_grow(n, edges, d, D, deadline):
    """Repeatedly add a vertex whose neighbourhood covers all vertices within D-1, while time remains."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, ball, full, d)
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k, annealed.
# Used with leftover time as a secondary family.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Plain projective plane for the largest prime power q with q + 1 <= d.
    pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    if pg_qs:
        consider(*lib.projective_plane_incidence(pg_qs[0]))
    if best_n >= moore:
        return best

    if D == 3:
        # Arc extensions: candidate q are those whose estimated bound beats the current best.
        cands = []
        for q in range(2, d - 1):
            if not lib.is_prime_power(q) or q > 23:
                continue
            s = d - q - 1
            if s < 1:
                continue
            m = q * q + q + 1
            bound = 2 * m + 2 * min(m, (m * s) // (q + 1))
            if bound > best_n:
                cands.append((q, m, s))

        if cands:
            arc_end = start + 0.85 * budget
            rem_m = sum(m for _, m, _ in cands)
            for q, m, s in cands:
                now = time.monotonic()
                slice_end = now + max(0.0, arc_end - now) * m / rem_m
                rem_m -= m
                _, edges, nbr = _pg_nbr(q)
                S = _ils(m, nbr, s, rng, slice_end, _conic_init(q))
                if S:
                    consider(*_arc_graph(m, edges, nbr, S))
            # Cover-based growth on the current best graph.
            n3, e3 = _cover_grow(best_n, best[1], d, D, start + 0.9 * budget)
            consider(n3, e3)

    # Secondary family: annealed group voltage lifts in the leftover time.
    ks = [1, 1, 2, 3] if D < 5 else [1, 2, 2, 3, 4]
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
