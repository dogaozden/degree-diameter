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

    Points are 0..P-1, lines are P..P+L-1. Returns (n, edges, P, index, lines), where
    index maps a normalized point vector to its id and lines is the list of point-id
    lists of the quadrangle's lines (line j is graph vertex P + j).
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
    return P + len(lines), edges, P, index, lines


# ----------------------------------------------------------------------------
# New helper: explicit regular spread of W(q), q odd.
#
# Identify F_q^4 with F_{q^2}^2 via X1 = x0 + x2*t, X2 = x3 + x1*t, where
# t^2 = nu is a non-square of F_q. The symplectic form of W(q) is then a
# constant multiple of Tr(t*(X1*Y2 - X2*Y1)), so each F_{q^2}-line
# {lambda*(A1, A2)} is a totally isotropic projective line of W(q). These
# q^2+1 lines partition the points: a spread, computed directly with no search.
# ----------------------------------------------------------------------------

def _regular_spread(q, index, lines):
    """Return graph line indices (into `lines`) of a regular spread of W(q), or None."""
    if q % 2 == 0:
        return None
    F = lib.GF(q)
    mul, add = F.mul, F.add
    minus1 = F.neg(1)
    nu = next((a for a in range(2, q) if F.pow(a, (q - 1) // 2) == minus1), None)
    if nu is None:
        return None

    def kmul(x, y):
        a, b = x
        c, d = y
        return (add(mul(a, c), mul(nu, mul(b, d))), add(mul(a, d), mul(b, c)))

    K = [(a, b) for a in range(q) for b in range(q) if (a, b) != (0, 0)]

    def pidx(v):
        c = next((x for x in v if x), 0)
        if c == 0:
            return None
        ic = F.inv(c)
        return index.get(tuple(mul(ic, x) for x in v))

    one = (1, 0)
    zero = (0, 0)
    gens = [(one, (c0, c1)) for c0 in range(q) for c1 in range(q)] + [(zero, one)]
    seen = bytearray(len(index))
    spread_sets = []
    for A1, A2 in gens:
        S = set()
        for lam in K:
            Y1 = kmul(lam, A1)
            Y2 = kmul(lam, A2)
            p = pidx((Y1[0], Y2[1], Y1[1], Y2[0]))
            if p is None:
                return None
            S.add(p)
        if len(S) != q + 1:
            return None
        for p in S:
            if seen[p]:
                return None
            seen[p] = 1
        spread_sets.append(S)
    if not all(seen):
        return None
    lineid = {frozenset(L): j for j, L in enumerate(lines)}
    ids = []
    for S in spread_sets:
        j = lineid.get(frozenset(S))
        if j is None:
            return None
        ids.append(j)
    return ids


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set, searched side by side.
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. A copy of u then has degree
# sum_{v in N(u)} m_v, so u may have at most one blown-up neighbour. Blown-up
# vertices on the same side must therefore have no common neighbour.
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
    """Large conflict-free subset of one side V, using conflict sets cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _ovoid_on_points(P, lines, deadline, rng, nprng):
    """Partial ovoid of W(q): a set of points, no two on a common line."""
    cs = [set() for _ in range(P)]
    for L in lines:
        for x in L:
            cs[x].update(L)
    for x in range(P):
        cs[x].discard(x)
    return _side_search(list(range(P)), cs, rng, nprng, deadline)


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (vertices in each component start at 0)."""
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
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
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
            n0, e0, P, index, lines = _gq(q)
            consider(n0, e0)
            sp = _regular_spread(q, index, lines)
            if sp is not None:
                # Every point then lies on exactly one blown line, so the only
                # remaining search is a partial ovoid on the points.
                cap = deadline if P > 100 else min(deadline, time.monotonic() + 2.0)
                ov = _ovoid_on_points(P, lines, cap, rng, nprng)
                S = list(ov) + [P + j for j in sp]
                consider(*_blow(n0, e0, S))
            else:
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
