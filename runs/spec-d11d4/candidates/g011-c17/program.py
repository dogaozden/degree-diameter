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
# Shared machinery: distance-2 conflict independent sets and twin blow-ups.
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
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set (joint search)."""
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
# NEW IDEA: side-split blow-up of a generalized quadrangle W(q).
#
# In the incidence graph of a GQ(q,q), a twin blow-up with multiplicity-2 set S
# is valid iff every point has at most one S-line through it (S-lines form a
# partial spread) and every line has at most one S-point on it (S-points form a
# partial ovoid). The two conditions involve disjoint sides, so the problem
# splits into two independent problems:
#   * a partial spread of lines, found by a randomised exact-cover DFS (which
#     can reach a full spread of q^2+1 lines, since W(q) always has one), with
#     an independent-set local search as a fallback;
#   * a partial ovoid of points, found by local search on the collinearity graph.
# Each side is solved in its own time slice. Partial results stay valid because
# any independent set is a legal choice.
# ----------------------------------------------------------------------------

def _spread_search(P, lmask, lines_of, rng, deadline, target):
    """Randomised DFS for pairwise-disjoint lines covering points, with restarts.

    Returns the largest partial spread found (list of line indices), possibly full.
    """
    best = []
    nodes = [0]
    limit = [0]

    def dfs(covered, chosen):
        if len(chosen) > len(best):
            best[:] = chosen
        if len(best) >= target:
            return True
        nodes[0] += 1
        if nodes[0] > limit[0] or time.monotonic() > deadline:
            return False
        bp = None
        for p in range(P):
            if (covered >> p) & 1:
                continue
            opts = [j for j in lines_of[p] if not (lmask[j] & covered)]
            if not opts:
                return False
            if bp is None or len(opts) < len(bp):
                bp = opts
                if len(opts) == 1:
                    break
        if bp is None:
            return False
        rng.shuffle(bp)
        for j in bp:
            chosen.append(j)
            if dfs(covered | lmask[j], chosen):
                return True
            chosen.pop()
        return False

    while time.monotonic() < deadline and len(best) < target:
        nodes[0] = 0
        limit[0] = 200
        dfs(0, [])
    return best


def _split_blowup(n0, edges0, q, rng, nprng, deadline):
    """Twin blow-up of W(q) by a partial ovoid (points) plus a partial spread (lines)."""
    P = q ** 3 + q ** 2 + q + 1
    L = n0 - P
    if L != P:
        return None
    lines_of = [[] for _ in range(P)]
    pts_of = [[] for _ in range(L)]
    for p, l in edges0:
        lines_of[p].append(l - P)
        pts_of[l - P].append(p)
    lmask = [0] * L
    for j in range(L):
        m = 0
        for p in pts_of[j]:
            m |= 1 << p
        lmask[j] = m

    # Conflict graphs: collinear points; concurrent lines.
    nb_pts = []
    for p in range(P):
        s = set()
        for j in lines_of[p]:
            s.update(pts_of[j])
        s.discard(p)
        nb_pts.append(sorted(s))
    nb_lines = []
    for j in range(L):
        s = set()
        for p in pts_of[j]:
            s.update(lines_of[p])
        s.discard(j)
        nb_lines.append(sorted(s))

    target = P // (q + 1)
    now = time.monotonic()
    avail = max(0.0, deadline - now)

    # Line side: exact-cover search for a spread, then ILS fallback.
    spread = _spread_search(P, lmask, lines_of, rng, now + 0.35 * avail, target)
    if len(spread) < target:
        cand = _independent_set(L, nb_lines, rng, nprng, time.monotonic() + 0.12 * avail)
        if len(cand) > len(spread):
            spread = cand

    # Point side: partial ovoid by local search with the remaining time.
    S_pts = _independent_set(P, nb_pts, rng, nprng, deadline)
    S_lines = [P + j for j in spread]
    return _blow(n0, edges0, list(S_pts) + S_lines)


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
        if D >= 4:
            n0, e0 = _gq(q)
            consider(n0, e0)
            res = _split_blowup(n0, e0, q, rng, nprng, deadline)
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
