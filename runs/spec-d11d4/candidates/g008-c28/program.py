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
    """Point-line incidence graph of the symplectic generalized quadrangle W(q) (fallback)."""
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


def _w_base(q):
    """W(q) built over K = GF(q^2) so that it contains an explicit spread.

    Points of PG(3,q) are nonzero vectors (x1, x2) in K^2 modulo GF(q)*. The
    alternating form Tr_{K/GF(q)}(x1*y2 - x2*y1) is nondegenerate, and every
    K-line {l*w : l in K} is totally isotropic and is a spread of the points.
    Returns (P, lines, spread): lines are sorted point lists, and spread holds
    the indices of q^2+1 pairwise disjoint lines. Returns None on failure.
    """
    Q2 = q * q
    F = lib.GF(Q2)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(Q2)]
    frob = [F.pow(a, q) for a in range(Q2)]
    tr = [A[a][frob[a]] for a in range(Q2)]
    sub = [a for a in range(1, Q2) if frob[a] == a]   # GF(q)*
    subz = [0] + sub

    def canon(x1, x2):
        return min((M[c][x1], M[c][x2]) for c in sub)

    pts, index = [], {}
    for x1 in range(Q2):
        for x2 in range(Q2):
            if x1 == 0 and x2 == 0:
                continue
            v = canon(x1, x2)
            if v not in index:
                index[v] = len(pts)
                pts.append(v)
    P = len(pts)

    def span_points(x, y):
        L = set()
        for a in subz:
            ax1, ax2 = M[a][x[0]], M[a][x[1]]
            for b in subz:
                v1 = A[ax1][M[b][y[0]]]
                v2 = A[ax2][M[b][y[1]]]
                if v1 or v2:
                    L.add(index[canon(v1, v2)])
        return sorted(L)

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
            if tr[t] != 0:
                continue
            L = span_points(x, y)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    if len(lines) != P:
        return None

    # Desarguesian spread: K*-orbits of K^2 points.
    spread_sets = []
    seen = bytearray(P)
    for p in range(P):
        if seen[p]:
            continue
        x = pts[p]
        L = sorted({index[canon(M[l][x[0]], M[l][x[1]])] for l in range(1, Q2)})
        for r in L:
            seen[r] = 1
        spread_sets.append(tuple(L))
    line_id = {tuple(L): j for j, L in enumerate(lines)}
    try:
        spread = [line_id[s] for s in spread_sets]
    except KeyError:
        return None
    return P, lines, spread


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace a vertex v in S by
# two twin copies with the same neighbourhood. A copy of u then has degree
# (d-1) + |N(u) cap S|, so S must meet every neighbourhood in at most one
# vertex: S is a set of base vertices with no two at distance 2.
#
# For W(q) the conflicts are collinear points and concurrent lines. A spread
# (q^2+1 lines, pairwise disjoint) is a maximum line-side set, so we fix it and
# search only the point side for a partial ovoid (pairwise non-collinear points).
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


def _collinear(P, lines):
    """For each point, the sorted list of other points sharing a line with it."""
    cs = [set() for _ in range(P)]
    for L in lines:
        for x in L:
            cs[x].update(L)
    return [sorted(s - {x}) for x, s in enumerate(cs)]


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


def _spread_blowup(q, deadline, rng, nprng):
    """Blow up W(q) by its explicit spread plus a searched partial ovoid."""
    base = _w_base(q)
    if base is None:
        return None
    P, lines, spread = base
    n0 = P + len(lines)
    edges0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
    nb = _collinear(P, lines)
    ovoid = _independent_set(P, nb, rng, nprng, deadline)
    S = [P + j for j in spread] + list(ovoid)
    return _blow(n0, edges0, S)


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set (fallback)."""
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
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 3.0)
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
        done = False
        if D >= 4:
            res = None
            try:
                res = _spread_blowup(q, deadline, rng, nprng)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])
                done = True
        if not done:
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
