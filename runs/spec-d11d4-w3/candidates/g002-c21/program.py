import itertools
import random
import time

import numpy as np

import lib


class _Timeout(Exception):
    pass


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
# W(q) from F_{q^2}^2 with an exact spread on the lines side.
#
# Points are F_q-orbits of nonzero vectors of F_Q^2 (Q = q^2). The collinearity
# relation is tr(x0*y1 - x1*y0) = 0, which is well defined on orbits.
# ----------------------------------------------------------------------------

def _symplectic_quadrangle(q):
    """Return (npts, lines, spread, pid, reps, F) for W(q), or None.

    pid[a*Q+b] is the point id of vector (a, b); reps[p] is a representative vector.
    """
    Q = q * q
    F = lib.GF(Q)
    mul, add, sub = F.mul, F.add, F.sub
    subfield = [x for x in range(Q) if F.pow(x, q) == x]
    if len(subfield) != q:
        return None
    scal = [x for x in subfield if x]
    tr = [add(z, F.pow(z, q)) for z in range(Q)]
    delta = 1

    pid = [-1] * (Q * Q)
    reps = []
    for a in range(Q):
        for b in range(Q):
            if (a or b) and pid[a * Q + b] < 0:
                k = len(reps)
                reps.append((a, b))
                for l in scal:
                    pid[mul(l, a) * Q + mul(l, b)] = k
    npts = len(reps)
    if npts != (Q * Q - 1) // (q - 1):
        return None

    def collinear(x, y):
        det = sub(mul(x[0], y[1]), mul(x[1], y[0]))
        return tr[mul(delta, det)] == 0

    covered = [set() for _ in range(npts)]
    lines = []
    for i in range(npts):
        x = reps[i]
        for j in range(i + 1, npts):
            if j in covered[i]:
                continue
            y = reps[j]
            if not collinear(x, y):
                continue
            L = set()
            for a in subfield:
                ax0, ax1 = mul(a, x[0]), mul(a, x[1])
                for b in subfield:
                    if a == 0 and b == 0:
                        continue
                    v0 = add(ax0, mul(b, y[0]))
                    v1 = add(ax1, mul(b, y[1]))
                    L.add(pid[v0 * Q + v1])
            if len(L) != q + 1:
                return None
            for p in L:
                covered[p] |= L
            lines.append(sorted(L))

    pdeg = [0] * npts
    for L in lines:
        for p in L:
            pdeg[p] += 1
    if any(c != q + 1 for c in pdeg):
        return None

    line_idx = {frozenset(L): j for j, L in enumerate(lines)}
    spread = []
    for v0, v1 in [(1, t) for t in range(Q)] + [(0, 1)]:
        key = frozenset(pid[mul(l, v0) * Q + mul(l, v1)] for l in range(1, Q))
        j = line_idx.get(key)
        if j is None:
            return None
        spread.append(j)
    if len(set(spread)) != Q + 1:
        return None
    return npts, lines, spread, pid, reps, F


# ----------------------------------------------------------------------------
# NEW HELPER: torus-invariant partial ovoids.
#
# The map (a, b) -> (mu*a, mu^-1*b) on F_Q^2 has determinant 1, so it preserves
# the symplectic form and acts on the points of W(q). For each divisor m of Q-1
# we take mu of order m, split the points into orbits of this cyclic group, drop
# orbits that contain a collinear pair, and solve a weighted maximum independent
# set on the orbit-conflict graph. The result is then completed greedily at point
# level. Searching orbits instead of points shrinks the problem a lot, so
# exact branch-and-bound often works on the quotient.
# ----------------------------------------------------------------------------

def _bnb(cands, adj, w, deadline):
    """Exact weighted max independent set by branch and bound (returns best found on timeout)."""
    best = [0, []]
    cnt = [0]

    def rec(cs, cur, chosen):
        cnt[0] += 1
        if (cnt[0] & 255) == 0 and time.monotonic() > deadline:
            raise _Timeout()
        if cur > best[0]:
            best[0] = cur
            best[1] = list(chosen)
        if not cs:
            return
        if cur + sum(w[c] for c in cs) <= best[0]:
            return
        v = cs[0]
        chosen.append(v)
        rec([c for c in cs[1:] if c not in adj[v]], cur + w[v], chosen)
        chosen.pop()
        rec(cs[1:], cur, chosen)

    try:
        rec(list(cands), 0, [])
    except _Timeout:
        pass
    return best[1]


def _greedy_wmis(valid, adj, w, rng, deadline):
    """Randomised greedy weighted independent set, restarted until the deadline."""
    best_tot, best_S = -1, []
    it = 0
    while it < 4000 and time.monotonic() < deadline:
        it += 1
        order = sorted(valid, key=lambda i: -(w[i] + 2.0 * rng.random()))
        blocked = set()
        S = []
        tot = 0
        for i in order:
            if i in blocked:
                continue
            S.append(i)
            tot += w[i]
            blocked |= adj[i]
            blocked.add(i)
        if tot > best_tot:
            best_tot, best_S = tot, S
    return best_S


def _complete(pts, C, rng):
    """Greedily extend an independent point set (C is the collinearity matrix with True diagonal)."""
    npts = C.shape[0]
    blocked = np.zeros(npts, dtype=bool)
    chosen = []
    for p in pts:
        blocked |= C[p]
        chosen.append(p)
    order = list(range(npts))
    rng.shuffle(order)
    for p in order:
        if not blocked[p]:
            chosen.append(p)
            blocked |= C[p]
    return chosen


def _orbit_ovoid(q, npts, pid, reps, F, deadline, rng):
    """Largest partial ovoid found by torus-orbit search, completed greedily."""
    Q = q * q
    G = Q - 1
    M = F.mul_table
    ADD = F.add_table
    NEG = np.array([F.neg(x) for x in range(Q)], dtype=np.int64)
    TR = np.array([F.add(z, F.pow(z, q)) for z in range(Q)], dtype=np.int64)
    R0 = np.array([r[0] for r in reps], dtype=np.int64)
    R1 = np.array([r[1] for r in reps], dtype=np.int64)
    det = ADD[M[R0[:, None], R1[None, :]], NEG[M[R1[:, None], R0[None, :]]]]
    C = TR[det] == 0
    np.fill_diagonal(C, True)
    Cn = C.astype(np.float32)
    np.fill_diagonal(Cn, 0.0)

    g = F.primitive_element()
    best, best_size = [], 0
    divisors = [m for m in range(2, G + 1) if G % m == 0]
    for m in divisors:
        if time.monotonic() >= deadline:
            break
        mu = F.pow(g, G // m)
        mui = F.inv(mu)
        orb = [-1] * npts
        orbits = []
        for p in range(npts):
            if orb[p] >= 0:
                continue
            k = len(orbits)
            members = []
            cur = p
            while orb[cur] < 0:
                orb[cur] = k
                members.append(cur)
                a, b = reps[cur]
                cur = pid[F.mul(mu, a) * Q + F.mul(mui, b)]
            orbits.append(members)
        K = len(orbits)
        I = np.zeros((npts, K), dtype=np.float32)
        I[np.arange(npts), np.asarray(orb)] = 1.0
        OC = (I.T @ Cn @ I) > 0.5
        w = [len(o) for o in orbits]
        valid = [i for i in range(K) if not OC[i, i]]
        adj = [set(np.nonzero(OC[i])[0].tolist()) - {i} for i in range(K)]
        dl = min(deadline, time.monotonic() + 1.5)
        if len(valid) <= 45:
            valid.sort(key=lambda i: -w[i])
            S = _bnb(valid, adj, w, dl)
        else:
            S = _greedy_wmis(valid, adj, w, rng, dl)
        pts = [p for i in S for p in orbits[i]]
        pts = _complete(pts, C, rng)
        if len(pts) > best_size:
            best, best_size = pts, len(pts)
    return best


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
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


def _ovoid_search(npts, lines, rng, nprng, deadline):
    """Large partial ovoid of the points: pairwise non-collinear point set."""
    nb = [set() for _ in range(npts)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    nbl = []
    for p in range(npts):
        s = nb[p]
        s.discard(p)
        nbl.append(sorted(s))
    return _independent_set(npts, nbl, rng, nprng, deadline)


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
        done = False
        if D >= 4:
            try:
                geo = _symplectic_quadrangle(q)
                if geo is not None:
                    npts, lines, spread, pid, reps, F = geo
                    n0 = npts + len(lines)
                    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
                    consider(n0, edges0)

                    try:
                        t = time.monotonic()
                        O1 = _orbit_ovoid(q, npts, pid, reps, F,
                                          min(deadline, t + 12.0), rng)
                    except Exception:
                        O1 = []
                    O2 = _ovoid_search(npts, lines, rng, nprng, deadline)
                    O = O1 if len(O1) >= len(O2) else list(O2)
                    S = list(O) + [npts + j for j in spread]
                    n, e = _blow(n0, edges0, S)
                    consider(n, e)
                    done = True
            except Exception:
                done = False

        if not done:
            if D >= 4:
                n0, e0 = _gq(q)
            elif D == 3:
                n0, e0 = lib.projective_plane_incidence(q)
            else:
                n0, e0 = 0, []
            if n0 > 0:
                consider(n0, e0)
                res = _blowup(n0, e0, d, deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
