import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction for D = 3: PG(2, q) incidence plus arc extension.
# ----------------------------------------------------------------------------

def _greedy_set(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy set S of points with every line holding <= s points of S
    and every point on <= s lines indexed by S."""
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return (max(cl, default=0) <= s) and (max(cp, default=0) <= s)


def _conic(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pg_base(d):
    """Arc-extended PG(2, q) for the largest prime power q with q + 1 <= d. Returns (n, edges) or None."""
    q = next((c for c in range(d - 1, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return None
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    if s < 1:
        return n2, edges
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    rng = random.Random(1)
    cands = [_greedy_set(m, s, pl, lp, rng, 30, time.monotonic() + 1.0)]
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        cs = _conic(q, index, F)
        if _loads_ok(cs, s, m, pl, lp):
            cands.append(cs)
    S = max(cands, key=len)
    if not S:
        return n2, edges
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in pl[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in lp[j]:
            E.append((Q, 2 * m + k + t))
    return n, E


# ----------------------------------------------------------------------------
# Insertion with annealed repair (bold path for D = 3).
# ----------------------------------------------------------------------------

def _bipartite_colors(n, adj):
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


def _bad_pairs(n, adj):
    """Number of unordered pairs at distance > 3 (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _accept(delta, T, rng):
    return delta <= 0 or rng.random() < math.exp(-delta / T)


def _repair(n, adj, color, d, rng, deadline, iters, T0):
    """Annealed repair: 2-switches and edge additions. Returns True iff bad pairs reach 0."""
    S0 = [v for v in range(n) if color[v] == 0]
    S1 = [v for v in range(n) if color[v] == 1]
    cost = _bad_pairs(n, adj)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (0.01 ** (it / iters))
        if rng.random() < 0.3:
            L0 = [v for v in S0 if len(adj[v]) < d]
            L1 = [v for v in S1 if len(adj[v]) < d]
            if not L0 or not L1:
                continue
            a = rng.choice(L0)
            b = rng.choice(L1)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _bad_pairs(n, adj)
            if _accept(new - cost, T, rng):
                cost = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            x1 = rng.choice(S0)
            x2 = rng.choice(S0)
            if x1 == x2 or not adj[x1] or not adj[x2]:
                continue
            y1 = rng.choice(list(adj[x1]))
            y2 = rng.choice(list(adj[x2]))
            if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
                continue
            adj[x1].remove(y1)
            adj[y1].remove(x1)
            adj[x2].remove(y2)
            adj[y2].remove(x2)
            adj[x1].add(y2)
            adj[y2].add(x1)
            adj[x2].add(y1)
            adj[y1].add(x2)
            new = _bad_pairs(n, adj)
            if _accept(new - cost, T, rng):
                cost = new
            else:
                adj[x1].remove(y2)
                adj[y2].remove(x1)
                adj[x2].remove(y1)
                adj[y1].remove(x2)
                adj[x1].add(y1)
                adj[y1].add(x1)
                adj[x2].add(y2)
                adj[y2].add(x2)
    return cost == 0


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 5.0)
    deadline = start + max(0.0, budget)

    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D != 3 or d < 3:
        return fallback

    base = _pg_base(d)
    if base is None:
        return fallback
    n, edges = base
    if not lib.is_valid(n, edges, d, D):
        return fallback
    best = (n, edges)

    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartite_colors(n, adj)
    rng = random.Random(seed * 2654435761 + d)

    while time.monotonic() < deadline:
        if all(len(adj[v]) >= d for v in range(n)):
            break
        c = rng.randrange(2)
        avail = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
        if not avail:
            c = 1 - c
            avail = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
            if not avail:
                break
        snap = [set(a) for a in adj]
        snap_n = n
        nb = rng.sample(avail, min(d, len(avail)))
        adj.append(set(nb))
        color.append(c)
        for u in nb:
            adj[u].add(n)
        n += 1

        ok = _repair(n, adj, color, d, rng, deadline, 400, 1.0)
        accepted = False
        if ok:
            E = [(u, v) for u in range(n) for v in adj[u] if u < v]
            if lib.is_valid(n, E, d, D):
                best = (n, E)
                accepted = True
        if not accepted:
            adj[:] = snap
            color[:] = color[:snap_n]
            n = snap_n

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
