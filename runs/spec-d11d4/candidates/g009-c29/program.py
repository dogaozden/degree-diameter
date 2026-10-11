import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (from parent program).
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
# Twin blow-up (from parent program).
# ----------------------------------------------------------------------------

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
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
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
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# New construction: cyclic Haar graphs found by local search.
#
# Haar graph H(m, S): a_i ~ b_{(i+s) mod m} for s in S, |S| = d. It is bipartite
# and d-regular on 2m vertices. Translations act transitively on each side, so
# the diameter is at most D iff the eccentricities of a_0 and b_0 are at most D.
# The search fixes 0 in S (WLOG) and minimises the number of vertices not reached
# within D steps from a_0 and b_0.
# ----------------------------------------------------------------------------

def _haar_cost(S, m, D):
    """Number of vertices not within distance D of a_0 or of b_0 (0 means diameter <= D)."""
    bad = 0
    for side in (0, 1):
        A = np.zeros(m, dtype=bool)
        B = np.zeros(m, dtype=bool)
        if side == 0:
            A[0] = True
        else:
            B[0] = True
        visA = A.copy()
        visB = B.copy()
        fa, fb = A, B
        for _ in range(D):
            nb = np.zeros(m, dtype=bool)
            for s in S:
                nb |= np.roll(fa, s)
            nb &= ~visB
            visB |= nb
            na = np.zeros(m, dtype=bool)
            for s in S:
                na |= np.roll(fb, -s)
            na &= ~visA
            visA |= na
            fa, fb = na, nb
        bad += 2 * m - int(visA.sum()) - int(visB.sum())
    return bad


def _haar_search(m, d, D, deadline, rng):
    """Local search for a connection set S (size d, containing 0) with diameter <= D."""
    if m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _haar_cost(S, m, D)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = list(S)
        T[i] = x
        c = _haar_cost(T, m, D)
        if c <= cur or rng.random() < 0.05:
            S, cur = T, c
    return S


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit - 3.0, 45.0))
    t_end = start + total
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

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

    if D == 2 and d < 2:
        return best

    # Phase 1: parent constructions (projective plane / generalized quadrangle
    # plus twin blow-up). Gets the first half of the budget.
    parent_end = start + 0.5 * total
    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < parent_end - 2.0:
        n0, e0 = 0, []
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, parent_end, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # Phase 2: cyclic Haar graphs with local search, using the remaining budget.
    if d >= 2 and D >= 2:
        m = max(d, best_n // 2 + 1)
        while True:
            remaining = t_end - time.monotonic()
            if remaining <= 0.5 or m < d:
                break
            chunk_end = time.monotonic() + max(1.0, 0.6 * remaining)
            chunk_end = min(chunk_end, t_end)
            S = _haar_search(m, d, D, chunk_end, rng)
            if S is None:
                break
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
