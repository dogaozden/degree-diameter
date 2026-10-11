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
# two copies (v, v') sharing the same neighbourhood. A copy of u then has degree
# (d-1) + |N(u) cap S| where S is the set of doubled vertices, so S must contain
# at most one neighbour of each u: no two vertices of S share a neighbour.
# Blow-ups keep bipartiteness and the diameter, so every such S gives a valid
# graph with n0 + |S| vertices.
#
# The conflict graph splits into two independent parts (one per bipartition
# side), since two vertices on opposite sides never have a common neighbour.
# Each side is searched separately with a fixed-k tabu search: find an
# independent set of size k by minimising the number of conflicting pairs,
# then grow k while the search succeeds.
# ----------------------------------------------------------------------------

def _kfixed(A, k, S0, rng, nprng, deadline, max_iter):
    """Tabu search for an independent set of size k in the conflict graph A (dense 0/1)."""
    N = A.shape[0]
    inS = np.zeros(N, dtype=bool)
    cnt = np.zeros(N, dtype=np.int64)   # number of neighbours inside S
    S = []
    for v in S0:
        if not inS[v]:
            inS[v] = True
            cnt += A[v]
            S.append(v)
    while len(S) < k:
        sc = np.where(inS, np.inf, cnt + nprng.random(N))
        v = int(np.argmin(sc))
        inS[v] = True
        cnt += A[v]
        S.append(v)
    cost = int(cnt[inS].sum()) // 2
    tab_in = np.zeros(N, dtype=np.int64)
    tab_out = np.zeros(N, dtype=np.int64)
    it = 0
    while cost > 0:
        if it >= max_iter:
            return False, S
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return False, S
        # Remove a conflicting vertex of S (most conflicts, not tabu).
        sc = np.where(inS & (tab_out <= it), cnt + nprng.random(N), -np.inf)
        u = int(np.argmax(sc))
        if not np.isfinite(sc[u]):
            u = S[rng.randrange(len(S))]
        inS[u] = False
        cost -= int(cnt[u])
        cnt -= A[u]
        S.remove(u)
        # Add the outside vertex with fewest conflicts with the rest of S (not tabu).
        sc = np.where((~inS) & (tab_in <= it), cnt + nprng.random(N), np.inf)
        v = int(np.argmin(sc))
        if not np.isfinite(sc[v]):
            v = u
        inS[v] = True
        cost += int(cnt[v])
        cnt += A[v]
        S.append(v)
        tab_in[u] = it + 7 + rng.randrange(10)
        tab_out[v] = it + 3 + rng.randrange(5)
    return True, S


def _max_indep(A, rng, nprng, deadline):
    """Grow k while the fixed-k search succeeds; return the largest independent set found."""
    N = A.shape[0]
    best = []
    S = []
    k = 1
    while k <= N and time.monotonic() < deadline:
        ok, S2 = _kfixed(A, k, S, rng, nprng, deadline, 400000)
        if not ok:
            break
        best = list(S2)
        S = S2
        k += 1
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
    # Bipartition by BFS 2-colouring.
    col = [-1] * n0
    for s in range(n0):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if col[y] == -1:
                    col[y] = 1 - col[x]
                    stack.append(y)
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    now = time.monotonic()
    mid = now + 0.5 * (deadline - now)
    S = []
    for c, dl in ((0, mid), (1, deadline)):
        verts = [v for v in range(n0) if col[v] == c]
        loc = {v: i for i, v in enumerate(verts)}
        m = len(verts)
        A = np.zeros((m, m), dtype=np.int32)
        for w in range(n0):
            if col[w] == c:
                continue
            nb = np.array([loc[x] for x in adj[w]], dtype=np.int64)
            A[np.ix_(nb, nb)] = 1
        np.fill_diagonal(A, 0)
        chosen = _max_indep(A, rng, nprng, dl)
        S.extend(verts[i] for i in chosen)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 3.0)
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
