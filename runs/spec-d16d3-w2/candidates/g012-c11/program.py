import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extension (proven baseline for D = 3).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, pl, lp) for PG(2, q): pl[P] = lines through P, lp[L] = points on L."""
    m2, edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _arc_search(m, s, pl, lp, rng, deadline):
    """Find a point set S where every line holds <= s points of S and every point lies on <= s lines of S.

    Greedy start plus iterated local search (insert with blocker removal). Returns the largest S seen.
    """
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in pl[P] if cl[L] >= s}
        satQ = {Q for Q in lp[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in pl[R]) or any(Q in satQ for Q in lp[R])]

    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if not blockers(P):
            add(P)
    best = list(S)
    while time.monotonic() < deadline:
        for _ in range(64):
            P = rng.randrange(m)
            if inS[P]:
                continue
            B = blockers(P)
            if not B:
                add(P)
            elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
                for R in B:
                    remove(R)
                add(P)
            else:
                continue
            if len(S) > len(best):
                best = list(S)
    return best


def _arc_graph(m, edges, pl, lp, S):
    """PG(2,q) incidence plus one new A-vertex per point of S and one new B-vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Generic helpers.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt.append(x)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _colour(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


# ----------------------------------------------------------------------------
# Repair-based growth: add one vertex, then anneal over degree-preserving
# rewires (and edge additions) until the diameter bound holds again.
# ----------------------------------------------------------------------------

def _grow_one(n, side, adj_in, E_in, d, D, rng, deadline, steps):
    """Try to add one vertex on a random side. Returns the new state (n, side, adj, E) or None."""
    adj = [set(a) for a in adj_in]
    E = [list(e) for e in E_in]
    side = list(side)

    c = rng.randrange(2)
    new = n
    side.append(c)
    adj.append(set())
    n += 1
    opp = [x for x in range(new) if side[x] != c and len(adj[x]) < d]
    rng.shuffle(opp)
    for x in opp[:d]:
        adj[x].add(new)
        adj[new].add(x)
        E.append([x, new])

    sides = [[], []]
    for v in range(n):
        sides[side[v]].append(v)

    cur = _bad(n, adj, D)
    T0, T1 = 1.0, 0.05
    for it in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / steps)

        if rng.random() < 0.1:
            # Edge addition between deficient opposite-side vertices (never worsens cost).
            da = [x for x in sides[0] if len(adj[x]) < d]
            db = [x for x in sides[1] if len(adj[x]) < d]
            if da and db:
                a = rng.choice(da)
                b = rng.choice(db)
                if b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    E.append([a, b])
                    cur = _bad(n, adj, D)
            continue

        # Rewire: edge (u, v) becomes (u, w), with w a deficient vertex on v's side.
        ei = rng.randrange(len(E))
        u, v = E[ei]
        dl = [x for x in sides[side[v]] if x != v and x not in adj[u] and len(adj[x]) < d]
        if not dl:
            continue
        w = rng.choice(dl)
        threshold = cur - T * math.log(1.0 - rng.random())
        adj[u].discard(v)
        adj[v].discard(u)
        adj[u].add(w)
        adj[w].add(u)
        c2 = _bad(n, adj, D)
        if c2 <= threshold:
            cur = c2
            E[ei] = [u, w]
        else:
            adj[u].discard(w)
            adj[w].discard(u)
            adj[u].add(v)
            adj[v].add(u)

    if cur != 0:
        return None
    return n, side, adj, [tuple(e) for e in E]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)
    if D == 2:
        return best_n, [tuple(e) for e in best_e]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Largest prime power q with q + 1 <= d.
    q = None
    for c in range(d - 1, 1, -1):
        if lib.is_prime_power(c):
            q = c
            break
    if q is None:
        return best_n, [tuple(e) for e in best_e]

    m, pg_e, pl, lp = _pg(q)
    consider(2 * m, pg_e)
    if best_n >= lib.moore_bound(d, D):
        return best_n, [tuple(e) for e in best_e]

    # Arc extension: spare capacity s = d - q - 1 per vertex.
    s = d - q - 1
    if s >= 1:
        arc_deadline = start + 0.2 * (hard - start)
        S = _arc_search(m, s, pl, lp, rng, arc_deadline)
        if S:
            an, ae = _arc_graph(m, pg_e, pl, lp, S)
            consider(an, ae)

    # Repair-based growth from the best graph found so far.
    cur_n = best_n
    cur_e = list(best_e)
    adj = [set() for _ in range(cur_n)]
    for u, v in cur_e:
        adj[u].add(v)
        adj[v].add(u)
    side = _colour(cur_n, adj)

    while time.monotonic() < hard and cur_n < lib.moore_bound(d, D):
        res = _grow_one(cur_n, side, adj, cur_e, d, D, rng, hard, steps=800)
        if res is None:
            continue
        cur_n, side, adj_new, cur_e = res
        adj = adj_new
        consider(cur_n, cur_e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, [tuple(e) for e in best_e]
