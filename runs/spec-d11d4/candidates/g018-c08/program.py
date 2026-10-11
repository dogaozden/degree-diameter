import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases from the parent (safe route, unchanged in substance).
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
# Twin blow-up (parent's route).
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
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
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
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# New route: bipartite group lifts of the 2-vertex base with d parallel darts.
#
# Vertices: A-copy x (0..N-1) and B-copy y (N..2N-1) for a group G of order N.
# A-vertex x is adjacent to B-vertex x*g for each g in S (|S| = d distinct).
# Left translations are automorphisms, so it suffices to check that the balls
# of radius D around the identity on side A and on side B cover everything.
# Search over S by a randomized local search that maximises coverage.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table code[x, g] = x*g for Z_m x|_r Z_k (k=1 gives the cyclic group Z_m)."""
    N = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    a_c = a[:, None]
    b_c = b[:, None]
    c = a[None, :]
    dd = b[None, :]
    return ((a_c + powers[b_c] * c) % m) * k + (b_c + dd) % k


def _cover(colsT, N, D, seed_side):
    """Number of vertices (both sides) within walk length D of the identity on the given side."""
    cov = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    cur = np.zeros(N, dtype=bool)
    cur[0] = True
    side = seed_side
    cov[side] |= cur
    for _ in range(D):
        nxt = np.zeros(N, dtype=bool)
        if side == 0:
            # A -> B: scatter x to x*g
            for idx in colsT:
                nxt[idx] |= cur
        else:
            # B -> A: gather x from x*g
            for idx in colsT:
                nxt |= cur[idx]
        cur = nxt
        side ^= 1
        cov[side] |= cur
    return int(cov[0].sum()) + int(cov[1].sum())


def _score(M, N, D, S):
    colsT = [np.ascontiguousarray(M[:, g]) for g in S]
    return _cover(colsT, N, D, 0) + _cover(colsT, N, D, 1)


def _search(M, N, d, D, deadline, rng):
    """Random-walk local search over connection sets S of size d maximising coverage."""
    full = 4 * N
    S = rng.sample(range(N), d)
    cur = _score(M, N, D, S)
    best_sc, best_S = cur, list(S)
    it = 0
    while best_sc < full:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        T = list(S)
        T[j] = new
        val = _score(M, N, D, T)
        if val >= cur or rng.random() < 0.01:
            S, cur = T, val
            if cur > best_sc:
                best_sc, best_S = cur, list(S)
    return best_sc, best_S


def _group_specs(N):
    """Group candidates of order N: cyclic Z_N, then semidirect products Z_m x| Z_k."""
    specs = [(N, 1, 1)]
    for k in range(2, 7):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                specs.append((m, k, r))
    return specs


def _lift_edges(M, N, S):
    edges = []
    for g in S:
        col = M[:, g].tolist()
        for x in range(N):
            edges.append((x, N + col[x]))
    return edges


def _group_route(d, D, best_n, deadline, rng, consider):
    cap = lib._moore_bound(d, D) // 2
    N = best_n // 2 + 1
    while N <= cap and time.monotonic() < deadline:
        for (m, k, r) in _group_specs(N):
            now = time.monotonic()
            if now >= deadline:
                return
            M = _table(m, k, r)
            slice_end = min(deadline, now + 1.0)
            sc, S = _search(M, N, d, D, slice_end, rng)
            if sc == 4 * N and len(S) == d:
                consider(2 * N, _lift_edges(M, N, S))
                break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 4.0)
    deadline = start + total
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

    group_route = (D >= 3 and d >= 5)
    blow_deadline = start + 0.45 * total if group_route else deadline

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < blow_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, blow_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # Bold route: group lifts of the 2-vertex base with d darts.
    if group_route and time.monotonic() < deadline - 1.0:
        try:
            _group_route(d, D, best_n, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
