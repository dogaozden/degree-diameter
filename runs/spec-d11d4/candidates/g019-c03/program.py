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

    Points are 0..P-1, lines are P..P+L-1. Returns (n, edges, P).
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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Twin blow-up.
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. A copy of u then has degree
# (d-1) + #{blown neighbours of u}, so each vertex may have at most one blown
# neighbour. Blown vertices on one side must therefore be "conflict-free" with
# respect to the opposite side. The two sides are independent of each other.
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
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _partial_spread(P, lines, deadline, rng, node_budget):
    """Randomized restarts of a depth-first exact-cover search.

    lines[j] is the list of point indices (0..P-1) on line j. Returns indices of
    pairwise disjoint lines: a full spread if one is found in time, otherwise the
    largest partial packing seen during the search.
    """
    L = len(lines)
    lm = [0] * L
    through = [[] for _ in range(P)]
    for j, pts in enumerate(lines):
        m = 0
        for p in pts:
            m |= 1 << p
            through[p].append(j)
        lm[j] = m
    full = (1 << P) - 1
    best = []

    while time.monotonic() < deadline:
        budget = [node_budget]
        chosen = []

        def dfs(covered):
            if len(chosen) > len(best):
                best[:] = chosen
            if covered == full:
                return True
            budget[0] -= 1
            if budget[0] <= 0:
                return False
            if (budget[0] & 255) == 0 and time.monotonic() >= deadline:
                budget[0] = 0
                return False
            bo = None
            for p in range(P):
                if (covered >> p) & 1:
                    continue
                opts = [j for j in through[p] if not (lm[j] & covered)]
                if not opts:
                    return False
                if bo is None or len(opts) < len(bo):
                    bo = opts
                    if len(opts) == 1:
                        break
            rng.shuffle(bo)
            for j in bo:
                chosen.append(j)
                if dfs(covered | lm[j]):
                    return True
                chosen.pop()
                if budget[0] <= 0:
                    return False
            return False

        if dfs(0):
            return list(best)
    return list(best)


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


def _blowup_sides(n0, edges0, d, V0, V1, deadline, rng, nprng, use_spread):
    """Twin blow-up of a base graph of degree d-1 with explicit sides V0, V1.

    With use_spread, the V1 side is first covered by a partial spread search
    (pairwise disjoint lines), which is the best possible structure for W(q).
    """
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

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    if use_spread:
        idx0 = {v: i for i, v in enumerate(V0)}
        lines_pts = [[idx0[w] for w in adj[Lv]] for Lv in V1]
        spread = _partial_spread(len(V0), lines_pts, now + 0.4 * total, rng, 2000)
        S_L = [V1[j] for j in spread]
        if len(spread) != len(V0) // (d - 1):
            rem_start = time.monotonic()
            rem = max(0.0, deadline - rem_start)
            ils = _side_search(V1, cs, rng, nprng, rem_start + 0.3 * rem)
            if len(ils) > len(S_L):
                S_L = ils
        S += S_L
        S += _side_search(V0, cs, rng, nprng, deadline)
    else:
        S += _side_search(V0, cs, rng, nprng, now + 0.5 * total)
        S += _side_search(V1, cs, rng, nprng, deadline)
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
        if D >= 4:
            try:
                n0, e0, P = _gq(q)
                consider(n0, e0)
                res = _blowup_sides(n0, e0, d, list(range(P)), list(range(P, n0)),
                                    deadline, rng, nprng, True)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass
        elif D == 3:
            try:
                n0, e0 = lib.projective_plane_incidence(q)
                m = n0 // 2
                consider(n0, e0)
                res = _blowup_sides(n0, e0, d, list(range(m)), list(range(m, n0)),
                                    deadline, rng, nprng, False)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
