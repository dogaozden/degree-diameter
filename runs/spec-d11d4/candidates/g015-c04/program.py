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
# Twin blow-up with a conflict-free vertex set on each side.
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. Every vertex x then has degree
# 10 + (number of blown neighbours of x), so x may have at most one blown
# neighbour. Blown vertices on the same side must therefore have no common
# neighbour. The two sides are independent, so each is searched separately.
# For W(q): a partial ovoid on points and a partial spread on lines.
#
# NEW: a perfect packing is a set of options (vertices of one side) whose
# neighbourhoods partition the opposite side. That is exactly a spread when the
# side is lines of W(q). It is optimal, since each option covers d-1 items.
# _perfect_packing finds one by randomized exact cover (minimum-remaining-value
# branching with restarts). Only when it fails does the local search run.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
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


def _perfect_packing(opts, K, rng, deadline):
    """Find options with pairwise disjoint item sets covering all K items, or None.

    opts[i] is the list of item indices (0..K-1) covered by option i. Randomized
    MRV backtracking: branch on the uncovered item with fewest available options,
    restarting with a new random order whenever a node budget is spent.
    """
    m = len(opts)
    if K == 0:
        return []
    if m == 0:
        return None
    item_opts = [[] for _ in range(K)]
    for i, its in enumerate(opts):
        for x in its:
            item_opts[x].append(i)
    if any(len(a) == 0 for a in item_opts):
        return None

    covered = [False] * K
    chosen = []
    budget = [0]

    def dfs(ncov):
        if ncov == K:
            return True
        budget[0] -= 1
        if budget[0] <= 0:
            return False
        if (budget[0] & 15) == 0 and time.monotonic() >= deadline:
            budget[0] = 0
            return False
        cnt = [[] for _ in range(K)]
        for i in range(m):
            its = opts[i]
            ok = True
            for x in its:
                if covered[x]:
                    ok = False
                    break
            if ok:
                for x in its:
                    cnt[x].append(i)
        best = -1
        bestkey = None
        for x in range(K):
            if covered[x]:
                continue
            c = len(cnt[x])
            if c == 0:
                return False
            key = (c, rng.random())
            if bestkey is None or key < bestkey:
                bestkey = key
                best = x
        cand = cnt[best]
        rng.shuffle(cand)
        for i in cand:
            its = opts[i]
            for x in its:
                covered[x] = True
            chosen.append(i)
            if dfs(ncov + len(its)):
                return True
            chosen.pop()
            for x in its:
                covered[x] = False
            if budget[0] <= 0:
                return False
        return False

    while time.monotonic() < deadline:
        covered[:] = [False] * K
        chosen.clear()
        budget[0] = 300
        if dfs(0):
            return list(chosen)
    return None


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (vertices in each component start at 0)."""
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
    done = [False, False]

    # Perfect packings first: a side whose neighbourhoods partition the other side
    # is the optimum for that side. Each attempt is capped, since a side with no
    # perfect packing (e.g. the points of W(q), q odd) would otherwise waste time.
    for c in (0, 1):
        V = sides[c]
        other = sides[1 - c]
        idx_o = {w: i for i, w in enumerate(other)}
        opts = [[idx_o[w] for w in adj[v]] for v in V]
        cap = min(deadline, time.monotonic() + 0.2 * total)
        res = _perfect_packing(opts, len(other), rng, cap)
        if res is not None:
            S += [V[i] for i in res]
            done[c] = True

    # Local search for the sides without a perfect packing, splitting the rest of the time.
    rem = max(0.0, deadline - time.monotonic())
    todo = [c for c in (0, 1) if not done[c]]
    for k, c in enumerate(todo):
        share = rem / (len(todo) - k)
        S += _side_search(sides[c], cs, rng, nprng, time.monotonic() + share)
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
