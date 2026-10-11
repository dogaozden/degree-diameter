import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (parent constructions, kept for the fallback path).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q)."""
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
# Independent-set search (iterated local search over a conflict graph).
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
            v = pick()
            if inS[v]:
                break
            add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if inS[v]:
                break
            add(v)
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: twin blow-up of the parabolic quadric Q(4,q).
#
# Q(4,q) is a generalized quadrangle of order (q,q), so its incidence graph is
# (q+1)-regular, bipartite, of diameter 4. Blowing up a set S of base vertices
# keeps validity iff every base vertex has at most one neighbour in S. Points
# of Q(4,q) and lines of Q(4,q) never conflict, so we take
#   S = (elliptic-quadric ovoid of points, size q^2+1)
#       union (partial spread of lines, found by local search).
# An ovoid is an exact hyperplane section Q(4,q) cap H with H elliptic; every
# line then meets it exactly once, which is what makes each line have only one
# S-neighbour. A partial spread is a set of pairwise disjoint lines.
# ----------------------------------------------------------------------------

def _quadric_gq(q):
    """Point-line incidence graph of Q(4,q): x0*x1 + x2*x3 + x4^2 = 0.

    Returns (P, L, edges, pts): points are 0..P-1, lines are P..P+L-1, pts lists
    the normalized coordinates of the points in index order.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    INV = [0] + [F.inv(a) for a in range(1, q)]
    two = A[1][1]

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    def Qf(v):
        s = M[v[0]][v[1]]
        s = A[s][M[v[2]][v[3]]]
        s = A[s][M[v[4]][v[4]]]
        return s

    def Bf(x, y):
        s = A[M[x[0]][y[1]]][M[x[1]][y[0]]]
        s = A[s][A[M[x[2]][y[3]]][M[x[3]][y[2]]]]
        return A[s][M[two][M[x[4]][y[4]]]]

    pts = []
    for v in itertools.product(range(q), repeat=5):
        if any(v) and next(c for c in v if c) == 1 and Qf(v) == 0:
            pts.append(v)
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            if Bf(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[M[a][x[k]]][M[b][y[k]]] for k in range(5))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P, len(lines), edges, pts


def _elliptic_ovoid(q, P, L, edges, pts):
    """Find a hyperplane H with H cap Q(4,q) an ovoid; return its point indices or None."""
    F = lib.GF(q)
    Pts = np.array(pts, dtype=np.int64)
    inc = np.zeros((P, L), dtype=np.int64)
    for p, l in edges:
        inc[p, l - P] = 1
    Mt = F.mul_table
    At = F.add_table
    target = q * q + 1
    for a in itertools.product(range(q), repeat=5):
        if not any(a) or next(c for c in a if c) != 1:
            continue
        prod = Mt[np.array(a, dtype=np.int64)[None, :], Pts]
        s = prod[:, 0]
        for k in range(1, 5):
            s = At[s, prod[:, k]]
        on = (s == 0)
        if int(on.sum()) != target:
            continue
        cnt = on.astype(np.int64) @ inc
        if np.all(cnt == 1):
            return [int(i) for i in np.nonzero(on)[0]]
    return None


def _quadric_blowup(q, d, qd, rng, nprng):
    """Blow-up of Q(4,q) by (elliptic ovoid) union (partial line spread)."""
    P, L, edges, pts = _quadric_gq(q)
    n0 = P + L
    deg = [0] * n0
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    if any(x != d - 1 for x in deg):
        return None
    O = _elliptic_ovoid(q, P, L, edges, pts)
    if O is None:
        return None
    through = [[] for _ in range(P)]
    for p, l in edges:
        through[p].append(l - P)
    nb_sets = [set() for _ in range(L)]
    for lst in through:
        for a in lst:
            for b in lst:
                if a != b:
                    nb_sets[a].add(b)
    nb = [sorted(s) for s in nb_sets]
    T = _independent_set(L, nb, rng, nprng, qd)
    S = list(O) + [P + j for j in T]
    return _blow(n0, edges, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.78 * time_limit - 3.0)
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

    # New route (D >= 4): blow-up of Q(4,q) with an elliptic ovoid.
    if D >= 4 and 3 <= q <= 11 and lib.is_prime_power(q):
        now = time.monotonic()
        if now < deadline - 3.0:
            qd = now + 0.6 * (deadline - now)
            try:
                res = _quadric_blowup(q, d, qd, rng, nprng)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])

    # Parent route, kept as a fallback: blow-up of W(q) / PG(2,q).
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        try:
            if D >= 4:
                n0, e0 = _gq(q)
            else:
                n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
