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
# Generic helpers.
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


def _adj_lists(n0, edges0):
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _blowup_joint(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set (joint search)."""
    adj = _adj_lists(n0, edges0)
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
# NEW IDEA: split the twin blow-up into two independent problems, and solve
# the line side as an EXACT SPREAD problem.
#
# In a base graph of degree d-1 (here W(q) with q = d-2), a twin blow-up on a
# set S is valid iff every vertex has at most one S-neighbour. Two distance-2
# conflicts exist only within a side of the bipartition, so S splits into:
#   * S_P: a set of points, no two collinear (a partial ovoid), and
#   * S_L: a set of lines, pairwise disjoint (a partial spread).
# The two parts never constrain each other, so the joint local search over
# both sides was wasteful. A FULL spread of W(q) (q^2+1 disjoint lines covering
# every point) is an exact cover, and an exact cover found by DFS with the
# minimum-remaining-values rule and random restarts is far more effective than
# local search. That gives |S_L| = q^2+1 = 82 for q = 9, and then only the
# partial ovoid remains to be searched by local search.
# ----------------------------------------------------------------------------

class _Stop(Exception):
    pass


def _exact_packing(P, sets, rng, deadline):
    """Pairwise-disjoint sets covering all P points (a spread), by randomized DFS with restarts.

    Returns the list of chosen set indices. If no full cover is found, returns the
    largest partial packing seen.
    """
    m = len(sets)
    inc = [[] for _ in range(P)]
    for j, s in enumerate(sets):
        for p in s:
            inc[p].append(j)
    best = []
    limit = 1500
    while time.monotonic() < deadline:
        covered = [False] * P
        blk = [0] * m          # blk[j] = number of covered points on set j
        chosen = []
        nodes = [0]
        cap = limit

        def dfs():
            nodes[0] += 1
            if nodes[0] > cap or ((nodes[0] & 31) == 0 and time.monotonic() >= deadline):
                raise _Stop
            bp = -1
            bc = 1 << 30
            bopts = None
            for p in range(P):
                if covered[p]:
                    continue
                opts = [j for j in inc[p] if blk[j] == 0]
                c = len(opts)
                if c < bc:
                    if c == 0:
                        return False
                    bc, bp, bopts = c, p, opts
            if bp < 0:
                return True
            rng.shuffle(bopts)
            for j in bopts:
                s = sets[j]
                for p in s:
                    covered[p] = True
                    for k in inc[p]:
                        blk[k] += 1
                chosen.append(j)
                if len(chosen) > len(best):
                    best[:] = chosen
                if dfs():
                    return True
                chosen.pop()
                for p in s:
                    covered[p] = False
                    for k in inc[p]:
                        blk[k] -= 1
            return False

        try:
            if dfs():
                return list(chosen)
        except _Stop:
            pass
        limit = int(limit * 1.2)
    return list(best)


def _structure(n0, edges0, P):
    """Return (line_pts, pnb, lnb): points of each line, collinear points, and concurrent lines."""
    L = n0 - P
    line_pts = [[] for _ in range(L)]
    pt_lines = [[] for _ in range(P)]
    for u, v in edges0:
        p, l = (u, v - P) if u < P else (v, u - P)
        line_pts[l].append(p)
        pt_lines[p].append(l)
    pnb = [set() for _ in range(P)]
    for pts in line_pts:
        for a in pts:
            pnb[a].update(pts)
    lnb = [set() for _ in range(L)]
    for ls in pt_lines:
        for a in ls:
            lnb[a].update(ls)
    pnb = [sorted(s - {i}) for i, s in enumerate(pnb)]
    lnb = [sorted(s - {i}) for i, s in enumerate(lnb)]
    return line_pts, pnb, lnb


def _decomposed_blowup(n0, e0, P, deadline, rng, nprng):
    """Blow up W(q) by a full spread of lines plus a partial ovoid of points."""
    line_pts, pnb, lnb = _structure(n0, e0, P)
    L = n0 - P
    now = time.monotonic()
    avail = max(0.1, deadline - now)
    k = len(line_pts[0])
    spread = _exact_packing(P, line_pts, rng, now + 0.45 * avail)
    if len(spread) * k < P:
        alt = _independent_set(L, lnb, rng, nprng, time.monotonic() + 0.1 * avail)
        if len(alt) > len(spread):
            spread = alt
    S_L = [P + j for j in spread]
    S_P = _independent_set(P, pnb, rng, nprng, deadline)
    return _blow(n0, e0, S_L + S_P)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 3.0)
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
            n0, e0, P = _gq(q)
            consider(n0, e0)
            try:
                res_edges = _decomposed_blowup(n0, e0, P, deadline, rng, nprng)
                consider(res_edges[0], res_edges[1])
            except Exception:
                pass
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup_joint(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
