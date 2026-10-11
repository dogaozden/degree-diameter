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
# Twin blow-up with a distance-2-free vertex set (from the parent).
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies sharing the same neighbourhood. A copy of u then has degree
# sum_{v in N(u)} m_v, which is at most d iff u has at most one neighbour in S.
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
# NEW IDEA: spare-capacity dominating extension.
#
# After a blow-up, many vertices have spare degree (degree < d). A new vertex x
# joined to a set N of spare vertices on the opposite side is a valid addition
# iff the graph stays bipartite (x is on the side opposite to N), degrees stay
# <= d, and every existing vertex w is within distance D-1 of some y in N
# (then dist(x, w) <= D). Adding a vertex never increases other distances, so
# the diameter of the rest of the graph is preserved. We find N by a greedy
# set cover over the (D-1)-balls, with random tie-breaking, and repeat while
# time remains.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _cover(reach, cands, full, d, rng):
    """Greedy cover of all bits of `full` by at most d masks from `cands`; None on failure."""
    covered = 0
    chosen = []
    avail = list(cands)
    while covered != full and len(chosen) < d and avail:
        best_i = -1
        best_key = None
        for i, y in enumerate(avail):
            sc = (reach[y] & ~covered).bit_count()
            key = (sc, rng.random())
            if best_key is None or key > best_key:
                best_key = key
                best_i = i
        if best_key[0] <= 0:
            return None
        y = avail[best_i]
        avail[best_i] = avail[-1]
        avail.pop()
        chosen.append(y)
        covered |= reach[y]
    if covered & full == full:
        return chosen
    return None


def _extend(n, edges, d, D, deadline, rng):
    """Greedily add vertices attached to spare-capacity vertices while time remains."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = _two_color(n, adj)
    spare = [d - len(a) for a in adj]
    R = D - 1
    while time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        reach = [1 << v for v in range(N)]
        for _ in range(R):
            new = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new.append(r)
            reach = new
        ok = False
        orders = [0, 1]
        rng.shuffle(orders)
        for t in orders:
            # New vertex has side t; its neighbours have side 1 - t.
            cands = [y for y in range(N) if side[y] == 1 - t and spare[y] > 0]
            if not cands:
                continue
            chosen = _cover(reach, cands, full, d, rng)
            if chosen is None:
                continue
            x = N
            adj.append([])
            for y in chosen:
                adj[y].append(x)
                adj[x].append(y)
                edges.append((y, x))
                spare[y] -= 1
            spare.append(d - len(chosen))
            side.append(t)
            ok = True
            break
        if not ok:
            break
    return len(adj), edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    ils_deadline = start + max(0.5, 0.6 * time_limit - 2.0)
    ext_deadline = start + max(0.8, 0.85 * time_limit - 3.0)
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < ils_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, ils_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
                if time.monotonic() < ext_deadline:
                    en, ee = _extend(res[0], res[1], d, D, ext_deadline, rng)
                    consider(en, ee)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
