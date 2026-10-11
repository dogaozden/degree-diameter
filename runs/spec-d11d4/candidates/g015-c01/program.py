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
# Twin blow-up.
#
# If every vertex of a base graph G has degree d-1, replace a set S of base
# vertices by twin pairs (copies share the neighbourhood). A copy of u then has
# degree sum_{v in N(u)} m_v, so the degree stays <= d iff every u has at most
# one neighbour in S. Hence S must be independent in the distance-2 conflict
# graph. Bipartiteness and diameter are preserved, so any such S gives a valid
# graph with n0 + |S| vertices, and lib.is_valid guards the result anyway.
#
# For W(q) the conflicts are collinear points and concurrent lines, and points
# never conflict with lines. So S = (partial ovoid on points) + (partial
# spread on lines), and the two halves are solved independently.
# ----------------------------------------------------------------------------

class _Abort(Exception):
    pass


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


def _line_masks(n0, P, edges0):
    """Bitmask of points for each line, and the list of lines through each point."""
    L = n0 - P
    lm = [0] * L
    pl = [[] for _ in range(P)]
    for u, v in edges0:
        if u < P:
            p, j = u, v - P
        else:
            p, j = v, u - P
        lm[j] |= 1 << p
        pl[p].append(j)
    return lm, pl


def _exact_spread(P, lm, pl, rng, deadline, node_limit):
    """Randomised DFS for a set of pairwise disjoint lines covering all P points.

    Returns a list of line indices, or None if no spread was found within the limits.
    """
    full = (1 << P) - 1
    nodes = [0]
    chosen = []

    def dfs(cov):
        if cov == full:
            return True
        nodes[0] += 1
        if nodes[0] > node_limit or ((nodes[0] & 255) == 0 and time.monotonic() >= deadline):
            raise _Abort()
        bopts = None
        for p in range(P):
            if (cov >> p) & 1:
                continue
            opts = [j for j in pl[p] if not (lm[j] & cov)]
            if not opts:
                return False
            if bopts is None or len(opts) < len(bopts):
                bopts = opts
                if len(opts) == 1:
                    break
        rng.shuffle(bopts)
        for j in bopts:
            chosen.append(j)
            if dfs(cov | lm[j]):
                return True
            chosen.pop()
        return False

    try:
        if dfs(0):
            return list(chosen)
    except _Abort:
        pass
    return None


def _line_packing(P, lm, pl, rng, deadline, node_limit):
    """Largest packing of pairwise disjoint lines found by randomised greedy and exact-cover DFS."""
    full = (1 << P) - 1
    best = []
    while True:
        order = list(range(len(lm)))
        rng.shuffle(order)
        cov = 0
        sel = []
        for j in order:
            if not (lm[j] & cov):
                cov |= lm[j]
                sel.append(j)
        if len(sel) > len(best):
            best = sel
        if cov == full:
            return sel
        if time.monotonic() >= deadline:
            break
        ex = _exact_spread(P, lm, pl, rng, deadline, node_limit)
        if ex is not None:
            return ex
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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
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

    now = time.monotonic()
    if n0 <= 60:
        deadline = min(deadline, now + 2.0)
    span = max(0.0, deadline - now)

    # Points and lines of a generalized quadrangle are equinumerous: n0 = 2P.
    P = n0 // 2
    S = _independent_set(n0, nb, rng, nprng, now + 0.5 * span)
    pts = [v for v in S if v < P]
    lns = [v - P for v in S if v >= P]

    lm, pl = _line_masks(n0, P, edges0)
    sel = _line_packing(P, lm, pl, rng, deadline, 20000)
    if len(sel) > len(lns):
        lns = sel

    S2 = pts + [P + j for j in lns]
    return _blow(n0, edges0, S2)


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
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
