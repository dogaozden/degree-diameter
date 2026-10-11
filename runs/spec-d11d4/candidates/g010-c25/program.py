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

    Points are 0..P-1, lines are P..P+L-1. Used as a fallback base.
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
# NEW: W(q) with an explicit line spread, built from F_{q^2}.
#
# Identify F_q^4 with F_{q^2}^2 via (a, b, c, d) -> (a + b*w, c + d*w), where w
# is an element of F_{q^2} outside F_q. The alternating F_q-form
#     B(x, y) = Tr(u1*v2 - u2*v1),   Tr(z) = z + z^q,
# is nondegenerate, so its totally isotropic lines form W(q) (a GQ of order
# (q, q)). The F_{q^2}-lines {lambda*u} are totally isotropic (det(lambda u,
# mu u) = 0) and partition the points of PG(3,q): they are a spread of W(q),
# of size q^2+1 = the largest possible partial spread. Fixing this spread on the
# line side leaves only the point side (a partial ovoid, searched) to optimise.
# ----------------------------------------------------------------------------

def _gq_spread(q):
    """Return (P, n0, edges0, lines, spread_vertex_ids) for W(q), or None."""
    Q2 = q * q
    F = lib.GF(Q2)
    S = [x for x in range(Q2) if F.pow(x, q) == x]          # subfield F_q
    if len(S) != q:
        return None
    w = next(x for x in range(Q2) if x not in S)
    NEG = np.array([F.neg(a) for a in range(Q2)], dtype=np.int64)
    ADD = F.add_table
    MUL = F.mul_table
    tr = np.array([F.add(z, F.pow(z, q)) for z in range(Q2)], dtype=np.int64)

    pts = [v for v in itertools.product(S, repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    pidx = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    U1 = np.array([F.add(a, F.mul(b, w)) for a, b, c, d in pts], dtype=np.int64)
    U2 = np.array([F.add(c, F.mul(d, w)) for a, b, c, d in pts], dtype=np.int64)
    # det(u_i, u_j) = U1[i]*U2[j] - U2[i]*U1[j], then trace to F_q.
    Dm = ADD[MUL[U1[:, None], U2[None, :]], NEG[MUL[U2[:, None], U1[None, :]]]]
    Z = (tr[Dm] == 0)

    # All totally isotropic lines (each found once via the covered matrix).
    covered = np.zeros((P, P), dtype=bool)
    lines = []
    for i in range(P):
        js = np.nonzero(Z[i, i + 1:] & ~covered[i, i + 1:])[0] + i + 1
        for j in js.tolist():
            if covered[i, j]:
                continue
            x, y = pts[i], pts[j]
            L = set()
            for a in S:
                for b in S:
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    L.add(pidx[norm(v)])
            L = sorted(L)
            lines.append(L)
            idx = np.array(L, dtype=np.int64)
            covered[np.ix_(idx, idx)] = True

    # F_{q^2}-coordinates decomposition: z = a + b*w  ->  (a, b).
    dec = {}
    for a in S:
        for b in S:
            dec[F.add(a, F.mul(b, w))] = (a, b)
    line_id = {frozenset(L): j for j, L in enumerate(lines)}

    spread = []
    used = set()
    for u1, u2 in [(1, t) for t in range(Q2)] + [(0, 1)]:
        Lset = set()
        for lam in range(1, Q2):
            a1, b1 = dec[F.mul(lam, u1)]
            a2, b2 = dec[F.mul(lam, u2)]
            Lset.add(pidx[norm((a1, b1, a2, b2))])
        j = line_id.get(frozenset(Lset))
        if j is None:
            return None
        spread.append(P + j)
        used |= Lset
    # Verify it really is a partition of the points.
    if len(spread) != Q2 + 1 or len(used) != P:
        return None
    if sum(len(lines[v - P]) for v in spread) != P:
        return None

    edges0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P, P + len(lines), edges0, lines, spread


def _gq_blowup(q, deadline, rng, nprng):
    """Blow up W(q): fixed spread on the line side, searched partial ovoid on the point side."""
    got = _gq_spread(q)
    if got is None:
        return None
    P, n0, edges0, lines, spread = got
    if P <= 100:
        deadline = min(deadline, time.monotonic() + 2.0)
    # Two points conflict if they are collinear (share a line).
    nb = [set() for _ in range(P)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    nbl = []
    for p in range(P):
        nb[p].discard(p)
        nbl.append(sorted(nb[p]))
    ovoid = _independent_set(P, nbl, rng, nprng, deadline)
    S = list(spread) + list(ovoid)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# Twin blow-up machinery (shared by the routes above).
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. A vertex then has degree
# 10 + (number of blown neighbours), so each vertex may have at most one blown
# neighbour. Blown vertices on the same side must have no common neighbour.
# ----------------------------------------------------------------------------

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


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        if v not in extra:
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
    deadline = start + max(0.5, 0.8 * time_limit - 4.0)
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
            res = _gq_blowup(q, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
            else:
                n0, e0 = _gq(q)
                consider(n0, e0)
                r2 = _blowup(n0, e0, d, deadline, rng, nprng)
                if r2 is not None:
                    consider(r2[0], r2[1])
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            r2 = _blowup(n0, e0, d, deadline, rng, nprng)
            if r2 is not None:
                consider(r2[0], r2[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
