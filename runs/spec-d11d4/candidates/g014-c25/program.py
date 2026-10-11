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
# Twin blow-up of a base graph whose vertices all have degree d-1.
#
# Cloning a vertex v (new vertex with the same neighbourhood) keeps bipartiteness
# and distances. A vertex x gains one degree per cloned neighbour, so the blow-up
# stays within degree d iff every vertex has at most one cloned neighbour.
# Hence the cloned set S must have no two vertices with a common neighbour.
# For W(q) the points of S form a partial ovoid and the lines form a partial
# spread; the two sides do not interact, so they are searched separately.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _sides(n, adj):
    """2-colouring of a bipartite graph (BFS)."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
    return col


def _conflicts(side, adj):
    """Local conflict lists on `side`: x ~ y iff x and y have a common neighbour."""
    pos = {v: i for i, v in enumerate(side)}
    cs = [set() for _ in side]
    for w in range(len(adj)):
        a = [pos[x] for x in adj[w] if x in pos]
        for i in range(len(a)):
            pi = a[i]
            for j in range(i + 1, len(a)):
                pj = a[j]
                cs[pi].add(pj)
                cs[pj].add(pi)
    return [sorted(s) for s in cs]


def _mis(N, nb, deadline, rng):
    """k-fixed tabu search for a large independent set. Returns local indices."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    inS = np.zeros(N, dtype=bool)
    c = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    BIG = 1 << 40

    def add(v):
        inS[v] = True
        S.append(v)
        if len(nbn[v]):
            c[nbn[v]] += 1

    def rem(u):
        inS[u] = False
        S.remove(u)
        if len(nbn[u]):
            c[nbn[u]] -= 1

    order = list(range(N))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    it = 0
    last = 0
    while time.monotonic() < deadline:
        it += 1
        Sarr = np.array(S, dtype=np.int64)
        cs = c[Sarr]
        conf = int(cs.sum()) // 2
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last = it
            score = c.copy()
            score[inS] = BIG
            s2 = score.copy()
            s2[tabu > it] = BIG
            if s2.min() < BIG:
                score = s2
            mn = score.min()
            if mn >= BIG:
                break
            cand = np.flatnonzero(score == mn)
            add(int(cand[rng.randrange(len(cand))]))
            continue
        # Conflicting: swap one member out, one outsider in (size kept fixed).
        ok = tabu[Sarr] <= it
        cu = np.where(ok, cs, -1)
        if cu.max() < 0:
            cu = cs
        mx = cu.max()
        cands = Sarr[cu == mx]
        u = int(cands[rng.randrange(len(cands))])
        rem(u)
        tabu[u] = it + 7 + rng.randrange(10)
        score = c.copy()
        score[inS] = BIG
        s2 = score.copy()
        s2[tabu > it] = BIG
        if s2.min() < BIG:
            score = s2
        mn = score.min()
        if mn >= BIG:
            add(u)
            break
        cand = np.flatnonzero(score == mn)
        v = int(cand[rng.randrange(len(cand))])
        add(v)
        tabu[v] = it + 3 + rng.randrange(5)
        if it - last > 30000:
            # Stagnation: restart from the best independent set found so far.
            for x in list(S):
                rem(x)
            for x in best:
                add(x)
            tabu[:] = 0
            last = it
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


def _blowup(n0, edges0, d, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 by a large admissible set."""
    adj = _adjacency(n0, edges0)
    if any(len(a) != d - 1 for a in adj):
        return None
    col = _sides(n0, adj)
    sides = [[v for v in range(n0) if col[v] == 0],
             [v for v in range(n0) if col[v] == 1]]
    now = time.monotonic()
    total = max(0.0, deadline - now)
    fracs = [0.6, 1.0]
    S = []
    for side, frac in zip(sides, fracs):
        dl = now + total * frac
        if len(side) <= 120:
            dl = min(dl, time.monotonic() + 2.0)
        nb = _conflicts(side, adj)
        local = _mis(len(side), nb, dl, rng)
        S.extend(side[i] for i in local)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 4.0)
    rng = random.Random(seed)

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

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Generalized quadrangle W(d-1) directly: degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        if time.monotonic() < deadline:
            consider(*_gq(d - 1))

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        n0, e0 = 0, []
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
