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
    """Point-line incidence graph of the symplectic generalized quadrangle W(q) (fallback route)."""
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


def _gq_regular(q):
    """W(q) incidence graph together with its regular spread (new construction).

    Idea: view F_q^4 as F_{q^2}^2 and use the symplectic form Tr(det(x, y)).
    The F_{q^2}-lines {lambda*v} are totally isotropic and partition the points,
    so they form a full spread of W(q) (q^2+1 lines). Blowing all of them up
    costs no search at all, leaving the ovoid side the whole time budget.

    Returns (n0, edges0, spread_ids) with base vertices: points 0..P-1, lines P..P+L-1.
    """
    Q = q * q
    F = lib.GF(Q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    K = [x for x in range(Q) if F.pow(x, q) == x]          # subfield F_q
    if len(K) != q:
        raise ValueError("subfield size mismatch")
    Kset = set(K)
    om = next(x for x in range(Q) if x not in Kset)         # F = K + K*om
    dec = {}
    for a in K:
        for b in K:
            dec[F.add(a, F.mul(b, om))] = (a, b)
    if len(dec) != Q:
        raise ValueError("decomposition failed")

    def tr(z):
        return F.add(z, F.pow(z, q))

    def fvec(u):
        return (F.add(u[0], F.mul(u[1], om)), F.add(u[2], F.mul(u[3], om)))

    def bil(u, v):
        x1, x2 = fvec(u)
        y1, y2 = fvec(v)
        return tr(F.sub(F.mul(x1, y2), F.mul(x2, y1)))

    E = [[1 if i == j else 0 for j in range(4)] for i in range(4)]
    G = [[bil(E[i], E[j]) for j in range(4)] for i in range(4)]

    def norm(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(M[ic][x] for x in v)

    pts = [v for v in itertools.product(K, repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    Gy = []
    for y in pts:
        row = []
        for i in range(4):
            s = 0
            for j in range(4):
                s = A[s][M[G[i][j]][y[j]]]
            row.append(s)
        Gy.append(row)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            gy = Gy[j]
            s = 0
            for k in range(4):
                s = A[s][M[x[k]][gy[k]]]
            if s != 0:
                continue
            y = pts[j]
            L = set()
            for a in K:
                ax = [M[a][x[k]] for k in range(4)]
                for b in K:
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

    n0 = P + len(lines)
    edges0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
    line_id = {frozenset(L): j for j, L in enumerate(lines)}

    # Regular spread: lines span{e(v), e(om*v)} = {e(lam*v) : lam in F*}.
    spread = []
    seen = set()
    for v1 in range(Q):
        for v2 in range(Q):
            if (v1, v2) == (0, 0) or (v1, v2) in seen:
                continue
            members = set()
            for lam in range(1, Q):
                w1, w2 = M[lam][v1], M[lam][v2]
                seen.add((w1, w2))
                c = (dec[w1][0], dec[w1][1], dec[w2][0], dec[w2][1])
                members.add(index[norm(c)])
            spread.append(frozenset(members))

    if len(spread) != q * q + 1:
        raise ValueError("wrong spread size")
    cover = [0] * P
    for S in spread:
        if len(S) != q + 1:
            raise ValueError("bad spread line")
        for p in S:
            cover[p] += 1
    if any(c != 1 for c in cover):
        raise ValueError("not a spread")
    spread_ids = [P + line_id[S] for S in spread]   # KeyError if not a base line
    return n0, edges0, spread_ids


# ----------------------------------------------------------------------------
# Twin blow-up.
#
# Blowing a vertex v into two twins preserves all distances, so the diameter is
# unchanged. A base vertex of degree d-1 may have at most one blown neighbour.
# On the line side we need a partial spread; on the point side a partial ovoid
# (no two blown points on a common line). These constraints are independent.
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


def _conflicts(n0, adj):
    """cs[x] = set of vertices sharing a neighbour with x."""
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    return cs


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


def _blowup_fixed(n0, edges0, d, spread_ids, deadline, rng, nprng):
    """Blow up the given full spread on the line side, then search an ovoid on the point side."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cnt = [0] * n0
    for s in spread_ids:
        for p in adj[s]:
            cnt[p] += 1
    if max(cnt) > 1:
        return None
    cs = _conflicts(n0, adj)
    color = _two_colour(n0, edges0)
    lc = color[spread_ids[0]]
    pts_side = [v for v in range(n0) if color[v] != lc]
    ovoid = _side_search(pts_side, cs, rng, nprng, deadline)
    S = list(dict.fromkeys(list(spread_ids) + list(ovoid)))
    return _blow(n0, edges0, S)


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Fallback: twin blow-up with spread search and ovoid search."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = _conflicts(n0, adj)
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.82 * time_limit - 4.0)
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

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            done = False
            try:
                n0, e0, spread_ids = _gq_regular(q)
                consider(n0, e0)
                res = _blowup_fixed(n0, e0, d, spread_ids, deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])
                done = True
            except Exception:
                done = False
            if not done and time.monotonic() < deadline - 2.0:
                n0, e0 = _gq(q)
                consider(n0, e0)
                res = _blowup(n0, e0, d, deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
