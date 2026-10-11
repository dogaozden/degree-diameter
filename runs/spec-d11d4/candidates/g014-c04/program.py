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
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree |N(u)| + #(S cap N(u)), so the degree is at most d iff u has at most
# one neighbour in S, where S is the set of doubled base vertices. So S must be
# a set of base vertices with no two at distance 2. A blow-up keeps
# bipartiteness and the diameter, so every such S yields a valid graph.
#
# For W(q) the conflicts are collinear points and concurrent lines. A spread of
# W(q) (q^2+1 pairwise disjoint lines) is a maximum-size conflict-free line set,
# so we first search for one by exact cover, then extend it with points via an
# iterated local search for a maximum independent set.
# ----------------------------------------------------------------------------

def _find_spread(P, line_sets, deadline, rng):
    """Find pairwise disjoint lines covering all P points (a spread).

    line_sets[j] is the list of point ids on line j. Returns the list of chosen
    line indices, or None if no spread was found before the deadline.
    Randomized depth-first exact cover with the most-constrained point first,
    restarted with a fresh random order after each node budget.
    """
    if P <= 0 or not line_sets:
        return None
    s = len(line_sets[0])
    if s == 0 or P % s or any(len(L) != s for L in line_sets):
        return None
    need = P // s
    lm = []
    point_lines = [[] for _ in range(P)]
    for j, L in enumerate(line_sets):
        mask = 0
        for p in L:
            mask |= 1 << p
            point_lines[p].append(j)
        lm.append(mask)
    full = (1 << P) - 1
    budget = [0]

    def dfs(cm, chosen):
        if cm == full:
            return list(chosen)
        budget[0] -= 1
        if budget[0] < 0:
            return None
        best_c = None
        for p in range(P):
            if (cm >> p) & 1:
                continue
            c = [j for j in point_lines[p] if not (lm[j] & cm)]
            if not c:
                return None
            if best_c is None or len(c) < len(best_c):
                best_c = c
                if len(c) == 1:
                    break
        rng.shuffle(best_c)
        for j in best_c:
            chosen.append(j)
            r = dfs(cm | lm[j], chosen)
            if r is not None:
                return r
            chosen.pop()
        return None

    while time.monotonic() < deadline:
        budget[0] = 300
        res = dfs(0, [])
        if res is not None and len(res) == need:
            return res
    return None


def _independent_set(N, nb, rng, nprng, deadline, init=()):
    """Iterated local search for a large set of vertices with no conflicting pair.

    init is an optional conflict-free starting set.
    """
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

    for v in init:
        if not inS[v]:
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


def _blowup(n0, edges0, d, P, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set.

    The first P base vertices are points and the rest are lines (for W(q));
    P = 0 disables the spread stage.
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
    if P > 0:
        now = time.monotonic()
        spread_deadline = now + 0.5 * max(0.0, deadline - now)
        found = _find_spread(P, [adj[v] for v in range(P, n0)], spread_deadline, rng)
        if found is not None:
            init = [P + j for j in found]

    S = _independent_set(n0, nb, rng, nprng, deadline, init)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 4.0)
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
            n0, e0 = _gq(q)
            P = (q + 1) * (q * q + 1)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            P = 0
        else:
            n0, e0, P = 0, [], 0
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, P, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
