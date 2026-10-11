import itertools
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
    Returns (n, edges, P).
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
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v, where m_v in {1, 2} is the class size. Since
# |N(u)| = d-1, the degree is at most d iff u has at most one neighbour in
# S = {v : m_v = 2}. So S must have no two vertices at distance 2.
#
# For W(q) the conflicts are collinear points and concurrent lines. A line
# spread (q^2+1 pairwise disjoint lines) is a maximum conflict-free line set,
# so we seed the search with an exact spread found by randomized DFS with MRV,
# then run iterated local search to add conflict-free points.
# ----------------------------------------------------------------------------

def _spread(P, pl, lp, target, rng, nprng, deadline, max_nodes=3000):
    """Find `target` lines that partition the P points (exact cover), or return []."""
    PL = np.asarray(pl, dtype=np.int64)   # (P, k): lines through each point
    LP = np.asarray(lp, dtype=np.int64)   # (L, k): points on each line
    while time.monotonic() < deadline:
        covered = np.zeros(P, dtype=bool)
        chosen = []
        nodes = [0]

        def dfs():
            if len(chosen) == target:
                return True
            nodes[0] += 1
            if nodes[0] > max_nodes:
                return False
            free = ~covered[LP].any(axis=1)
            cnt = free[PL].sum(axis=1).astype(float)
            score = np.where(covered, 1e9, cnt + 0.5 * nprng.random(P))
            p = int(np.argmin(score))
            if score[p] >= 1e9 or cnt[p] == 0:
                return False
            cands = [int(l) for l in PL[p] if free[l]]
            rng.shuffle(cands)
            for l in cands:
                pts = LP[l]
                covered[pts] = True
                chosen.append(l)
                if dfs():
                    return True
                covered[pts] = False
                chosen.pop()
                if nodes[0] > max_nodes:
                    return False
            return False

        if dfs():
            return list(chosen)
    return []


def _independent_set(N, nb, rng, nprng, deadline, init=()):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
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
        score = cnt + nprng.random(N)     # random tie-breaking
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    # Warm start from a conflict-free initial set.
    for v in init:
        if not inS[v] and cnt[v] == 0:
            add(v)

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


def _blowup(n0, edges0, d, deadline, rng, nprng, P=None):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set.

    If P is given (bipartite base with points 0..P-1 and lines P..n0-1, as in
    W(q)), first seed the search with an exact line spread.
    """
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
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

    init = []
    if P is not None:
        pl = [[] for _ in range(P)]
        lp = [[] for _ in range(n0 - P)]
        for u, v in edges0:
            pl[u].append(v - P)
            lp[v - P].append(u)
        if all(len(x) == d - 1 for x in pl) and all(len(x) == d - 1 for x in lp):
            if P % (d - 1) == 0:
                target = P // (d - 1)
                now = time.monotonic()
                sp_deadline = now + 0.6 * max(0.0, deadline - now)
                spread = _spread(P, pl, lp, target, rng, nprng, sp_deadline)
                init = [P + l for l in spread]

    S = _independent_set(n0, nb, rng, nprng, deadline, init)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 3.0)
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

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0, P = _gq(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng, P)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng, None)
        else:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
