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


def _gq_parts(q):
    """Symplectic generalized quadrangle W(q): (P, lines) with points 0..P-1 and lines as sorted point lists."""
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
    return P, lines


def _gq_incidence(P, lines):
    """Incidence graph from parts: points 0..P-1, lines P..P+L-1."""
    return P + len(lines), [(p, P + j) for j, L in enumerate(lines) for p in L]


# ----------------------------------------------------------------------------
# Spread search (exact cover of points by pairwise disjoint lines), randomized
# DFS with fewest-options branching and restarts.
# ----------------------------------------------------------------------------

def _spread(P, lines, k, deadline, rng):
    """Return k pairwise disjoint line indices covering all points, or None."""
    lmask = [sum(1 << p for p in Ls) for Ls in lines]
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    node_limit = 400
    while time.monotonic() < deadline:
        nodes = [0]

        def dfs(cov, chosen):
            if len(chosen) == k:
                return True
            nodes[0] += 1
            if nodes[0] > node_limit or time.monotonic() > deadline:
                return False
            bestopts = None
            for p in range(P):
                if (cov >> p) & 1:
                    continue
                opts = [l for l in pl[p] if not (lmask[l] & cov)]
                if bestopts is None or len(opts) < len(bestopts):
                    bestopts = opts
                    if len(opts) <= 1:
                        break
            if not bestopts:
                return False
            rng.shuffle(bestopts)
            for l in bestopts:
                chosen.append(l)
                if dfs(cov | lmask[l], chosen):
                    return True
                chosen.pop()
            return False

        chosen = []
        if dfs(0, chosen):
            return chosen
    return None


# ----------------------------------------------------------------------------
# Conflict-free subset search (iterated tabu search on a conflict graph).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    if N == 0:
        return []
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


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


# ----------------------------------------------------------------------------
# Twin blow-up. Blowing up a set B of base vertices (each base vertex of degree
# d-1) is valid iff every vertex has at most one blown neighbour. For W(q) this
# means: blown points form a partial ovoid, blown lines form a partial spread,
# and the two sides are independent.
# ----------------------------------------------------------------------------

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


def _gq_blow(P, lines, q, deadline, rng, nprng):
    """Choose blown points (partial ovoid) and blown lines (spread, else partial spread)."""
    now = time.monotonic()
    total = max(0.0, deadline - now)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    k = P // (q + 1)
    spread = _spread(P, lines, k, now + 0.4 * total, rng)
    if spread is not None:
        Lset = spread
    else:
        Lset = _independent_set(L, [sorted(s) for s in ladj], rng, nprng,
                                time.monotonic() + 0.3 * total)
    pset = _independent_set(P, [sorted(s) for s in padj], rng, nprng, deadline)
    return list(pset) + [P + j for j in Lset]


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


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Generic twin blow-up of a base graph of degree d-1, searching each side separately."""
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
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]
    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 5.0)
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            P, lines = _gq_parts(q)
            n0, e0 = _gq_incidence(P, lines)
            consider(n0, e0)
            S = _gq_blow(P, lines, q, deadline, rng, nprng)
            n1, e1 = _blow(n0, e0, S)
            consider(n1, e1)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
