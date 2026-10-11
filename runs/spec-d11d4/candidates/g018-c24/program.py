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
# NEW IDEA: spread + ovoid twin blow-up of a generalized quadrangle.
#
# Twin blow-up of a base graph G where every vertex has degree d-1: a set S of
# base vertices is blown into twin pairs. Copies of u get degree
# sum_{v in N(u)} m_v, so it is <= d iff u has at most one neighbour in S.
# For W(q) (points P, lines L, both of size (q+1)(q^2+1)) the admissible S are
#   S_points: pairwise non-collinear points (a partial ovoid), and
#   S_lines : pairwise disjoint lines (a partial spread),
# and the two parts never interact (they are on different sides). A full spread
# has q^2+1 lines and covers every point exactly once, so it is the best
# possible spread part. This routine finds a full spread by randomized exact
# cover (DLX-style, MRV branching with node budgets and restarts), then runs
# iterated local search for the ovoid part alone.
# ----------------------------------------------------------------------------

def _cover_attempt(P, size, line_pts, pt_lines, rng, budget0):
    """One randomized search for a perfect cover of points by disjoint lines."""
    L = len(line_pts)
    covered = [False] * P
    avail = [True] * L
    chosen = []
    state = {"ncov": 0, "budget": budget0}

    def rec():
        if state["ncov"] == P:
            return True
        if state["budget"] <= 0:
            return False
        state["budget"] -= 1
        best_opts = None
        for p in range(P):
            if covered[p]:
                continue
            opts = [j for j in pt_lines[p] if avail[j]]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
                if len(opts) == 1:
                    break
        rng.shuffle(best_opts)
        for j in best_opts:
            pts = line_pts[j]
            for p in pts:
                covered[p] = True
            state["ncov"] += size
            removed = []
            for p in pts:
                for k in pt_lines[p]:
                    if avail[k]:
                        avail[k] = False
                        removed.append(k)
            chosen.append(j)
            if rec():
                return True
            chosen.pop()
            for k in removed:
                avail[k] = True
            state["ncov"] -= size
            for p in pts:
                covered[p] = False
            if state["budget"] <= 0:
                return False
        return False

    if rec():
        return list(chosen)
    return None


def _spread_cover(P, line_pts, rng, deadline):
    """Find a spread (disjoint lines covering all P points) by restarted randomized search."""
    if not line_pts:
        return None
    size = len(line_pts[0])
    if any(len(x) != size for x in line_pts) or P % size != 0:
        return None
    pt_lines = [[] for _ in range(P)]
    for j, pts in enumerate(line_pts):
        for p in pts:
            pt_lines[p].append(j)
    while time.monotonic() < deadline:
        res = _cover_attempt(P, size, line_pts, pt_lines, rng, 400)
        if res is not None:
            return res
    return None


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


def _blow_spread_ovoid(n0, edges0, d, deadline, rng, nprng):
    """Blow up a GQ incidence graph by a full spread (lines) plus a partial ovoid (points)."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    if n0 % 2:
        return None
    P = n0 // 2
    if any((u < P) == (v < P) for u, v in edges0):
        return None
    line_pts = [sorted(adj[P + j]) for j in range(P)]
    spread = _spread_cover(P, line_pts, rng, min(deadline, time.monotonic() + 20.0))
    if spread is None:
        return None
    S_lines = [P + j for j in spread]
    # Ovoid part: points conflict when collinear (share a line).
    cs = [set() for _ in range(P)]
    for pts in line_pts:
        for a in pts:
            for b in pts:
                if a != b:
                    cs[a].add(b)
    nb = [sorted(s) for s in cs]
    ov = _independent_set(P, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S_lines + ov)


# ----------------------------------------------------------------------------
# Older generic twin blow-up (used for PG(2,q) and as fallback).
# ----------------------------------------------------------------------------

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
        n0, e0 = 0, []
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        if n0 > 0:
            consider(n0, e0)
            res = None
            if D >= 4:
                res = _blow_spread_ovoid(n0, e0, d, deadline, rng, nprng)
            if res is None:
                res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
