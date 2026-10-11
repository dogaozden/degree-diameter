import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up (parent construction).
#
# Blowing a vertex v into two twins preserves all distances between original
# vertices. Each neighbour of a blown vertex gains one degree, so on each side
# we need pairwise disjoint neighbourhoods: a partial spread (side A) and a
# partial ovoid (side B), found by randomized search.
# ----------------------------------------------------------------------------

def _spread_search(A_nb, B_to_A, nB, k, rng, deadline):
    """Largest family of A-vertices with pairwise disjoint neighbourhoods (k each)."""
    nA = len(A_nb)
    blocked = [0] * nA
    covered = [False] * nB
    chosen = []
    best = []
    stop = [False]
    steps = [0]
    cap = [0]
    order = list(range(nB))

    def rec(U):
        if stop[0]:
            return
        steps[0] += 1
        if steps[0] > cap[0] or ((steps[0] & 15) == 0 and time.monotonic() >= deadline):
            stop[0] = True
            return
        if len(chosen) > len(best):
            best[:] = chosen
        if U == 0 or len(chosen) + U // k <= len(best):
            return
        pick = None
        for b in order:
            if covered[b]:
                continue
            o = [a for a in B_to_A[b] if blocked[a] == 0]
            if not o:
                return
            if pick is None or len(o) < len(pick):
                pick = o
        rng.shuffle(pick)
        for a in pick:
            chosen.append(a)
            for x in A_nb[a]:
                covered[x] = True
                for a2 in B_to_A[x]:
                    blocked[a2] += 1
            rec(U - k)
            for x in A_nb[a]:
                covered[x] = False
                for a2 in B_to_A[x]:
                    blocked[a2] -= 1
            chosen.pop()
            if stop[0]:
                return

    while time.monotonic() < deadline and len(best) * k < nB:
        rng.shuffle(order)
        stop[0] = False
        cap[0] = steps[0] + 600
        rec(nB)
    return list(best)


def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    if N == 0:
        return []

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)

    A_list = sides[1]
    B_list = sides[0]
    idxB = {v: i for i, v in enumerate(B_list)}
    A_nb = [[idxB[w] for w in adj[v]] for v in A_list]
    B_to_A = [[] for _ in B_list]
    for ai, nbs in enumerate(A_nb):
        for b in nbs:
            B_to_A[b].append(ai)
    res = _spread_search(A_nb, B_to_A, len(B_list), d - 1, rng, now + 0.5 * total)
    S = [A_list[ai] for ai in res]

    S += _side_search(sides[0], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW: dominating-set vertex insertion.
#
# Adding a vertex x adjacent to a set N cannot lengthen any existing distance.
# Distances from x are 1 + dist(N, w), so x keeps diameter D exactly when every
# vertex w lies within distance D-1 of N. We therefore look for a set N of at
# most d "spare" vertices (degree < d) on one colour class that dominates the
# whole graph within radius D-1. Domination is found by simulated annealing on
# bitmask balls; each success adds one vertex and consumes d spare degrees.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            m = reach[v]
            for u in adj[v]:
                m |= reach[u]
            new.append(m)
        reach = new
    return reach


def _dominate(R, C, k, full, rng, deadline, iters):
    """Find k candidates from C whose radius balls (masks R) cover all of full."""
    cur = rng.sample(C, k)
    cv = 0
    for s in cur:
        cv |= R[s]
    curf = (full ^ cv).bit_count()
    T = 2.0
    for it in range(iters):
        if curf == 0:
            return cur
        if (it & 1023) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        c = C[rng.randrange(len(C))]
        if c in cur:
            continue
        new = cur[:]
        new[i] = c
        cv = 0
        for s in new:
            cv |= R[s]
        nf = (full ^ cv).bit_count()
        if nf <= curf or rng.random() < math.exp((curf - nf) / T):
            cur, curf = new, nf
        T = max(0.1, T * 0.9998)
    return cur if curf == 0 else None


def _dominating_insertion(n, edges, d, D, deadline, rng, iters=30000):
    """Repeatedly add vertices whose neighbourhoods dominate the graph within D-1."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_colour(n, edges)
    while time.monotonic() < deadline:
        R = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for c in sides:
            C = [v for v in range(n) if color[v] == c and len(adj[v]) < d]
            if len(C) < d:
                continue
            S = _dominate(R, C, d, full, rng, deadline, iters)
            if S is not None:
                x = n
                adj.append([])
                color.append(1 - c)
                for s in S:
                    adj[s].append(x)
                    adj[x].append(s)
                    edges.append((s, x))
                n += 1
                placed = True
                break
        if not placed:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 4.0)
    deadline = start + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q):
        if D >= 4:
            n0, e0 = _gq(q)
        else:
            n0, e0 = lib.projective_plane_incidence(q)

        # Route B: dominating-set insertion directly on the base graph.
        ins_deadline = start + 0.2 * budget
        if time.monotonic() < ins_deadline:
            nb_, eb_ = _dominating_insertion(n0, e0, d, D, ins_deadline, rng)
            consider(nb_, eb_)

        # Route A: twin blow-up, then insertion on the blown-up graph.
        blow_deadline = start + 0.6 * budget
        if time.monotonic() < blow_deadline:
            res = _blowup(n0, e0, d, blow_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
                na, ea = _dominating_insertion(res[0], res[1], d, D, deadline, rng)
                consider(na, ea)
        else:
            consider(n0, e0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
