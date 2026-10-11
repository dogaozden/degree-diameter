import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# NEW HELPER: explicit spread of W(q) for odd q, computed over the subfield
# K = GF(q) of F = GF(q^2). No search is needed.
#
# A point of PG(3,q) is x = (x0,x1,x2,x3) with entries in K. Map it to
#     z1 = x0 + x2*theta,   z2 = x1 + n^{-1} * x3 * theta   in F = GF(q^2),
# where theta is in F \ K with theta^2 = n in K. The symplectic form of W(q),
#     B(x,y) = x0 y1 - x1 y0 + x2 y3 - x3 y2,
# equals the K-part of det(z,z') = z1 z2' - z2 z1'. Each F-line {lam*(1,t)} has
# det = 0, so its K-points are totally isotropic, i.e. a line of W(q). The
# q^2+1 such lines are pairwise disjoint and cover all points: a spread.
# Blowing up every spread line gives each point degree 1 + (q+1) = d.
# ----------------------------------------------------------------------------


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _wq_model(q):
    """Return (pts, lines, spread) for W(q), built over the subfield K = GF(q) of GF(q^2).

    pts: normalised vectors of K^4 (K-indices). lines: sorted lists of point indices.
    spread: list of q^2+1 line indices forming a spread (odd q, explicit), else None.
    """
    F = lib.GF(q * q)
    K = range(q)
    kel = [x for x in range(q * q) if F.pow(x, q) == x]
    if len(kel) != q:
        return None
    kidx = {x: i for i, x in enumerate(kel)}
    kadd = [[kidx[F.add(kel[i], kel[j])] for j in K] for i in K]
    kmul = [[kidx[F.mul(kel[i], kel[j])] for j in K] for i in K]
    kneg = [kidx[F.neg(kel[i])] for i in K]
    ZERO, ONE = kidx[0], kidx[1]
    kinv = [ZERO] * q
    for i in K:
        if i != ZERO:
            kinv[i] = kidx[F.inv(kel[i])]

    def norm(v):
        c = next(x for x in v if x != ZERO)
        ic = kinv[c]
        return tuple(kmul[ic][x] for x in v)

    pts = [v for v in itertools.product(K, repeat=4)
           if any(x != ZERO for x in v) and norm(v) == v]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def sym(x, y):
        t = kadd[kmul[x[0]][y[1]]][kneg[kmul[x[1]][y[0]]]]
        s = kadd[kmul[x[2]][y[3]]][kneg[kmul[x[3]][y[2]]]]
        return kadd[t][s]

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            if sym(x, y) != ZERO:
                continue
            L = {i, j}
            for a in K:
                for b in K:
                    if a == ZERO and b == ZERO:
                        continue
                    v = tuple(kadd[kmul[a][x[k]]][kmul[b][y[k]]] for k in range(4))
                    L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1

    spread = None
    try:
        theta = next(z for z in range(q * q)
                     if F.pow(z, q) != z and F.pow(F.mul(z, z), q) == F.mul(z, z))
    except StopIteration:
        theta = None
    if theta is not None:
        dec = {}
        for a in K:
            for b in K:
                dec[F.add(kel[a], F.mul(kel[b], theta))] = (a, b)
        nidx = kidx[F.mul(theta, theta)]
        line_id = {tuple(L): j for j, L in enumerate(lines)}
        sp = []
        ok = len(dec) == q * q
        for t in [None] + list(range(q * q)):
            if not ok:
                break
            pset = set()
            for lam in range(1, q * q):
                if t is None:
                    z1, z2 = 0, lam
                else:
                    z1, z2 = lam, F.mul(lam, t)
                a1, b1 = dec[z1]
                a2, b2 = dec[z2]
                pset.add(index[norm((a1, a2, b1, kmul[nidx][b2]))])
            j = line_id.get(tuple(sorted(pset)))
            if j is None:
                ok = False
                break
            sp.append(j)
        if ok and len(set(sp)) == q * q + 1:
            covered_pts = set()
            for j in sp:
                covered_pts.update(lines[j])
            if len(covered_pts) == P:
                spread = sp
    return pts, lines, spread


# ----------------------------------------------------------------------------
# Independent-set search for twin blow-ups.
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
            if len(S) > len(best):
                best = list(S)
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
    if conf == 0 and len(S) > len(best):
        best = list(S)
    return best


def _ils(N, groups, deadline, rng, nprng):
    """Large set of vertices in 0..N-1 such that no two share a group."""
    nb = [set() for _ in range(N)]
    for g in groups:
        for a in g:
            nb[a].update(g)
    nb = [sorted(x for x in s if x != v) for v, s in enumerate(nb)]
    return _independent_set(N, nb, rng, nprng, deadline)


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


def _blow_generic(n0, edges0, deadline, rng, nprng):
    """Twin blow-up of a regular base graph of degree d-1 (conflicts = common neighbour)."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    S = _ils(n0, adj, deadline, rng, nprng)
    return _blow(n0, edges0, S)


def _blow_wq(q, deadline, rng, nprng):
    """Blow up W(q) (degree q+1, d = q+2). Odd q: explicit spread on lines, search on points."""
    m = _wq_model(q)
    if m is None:
        return None
    pts, lines, spread = m
    P = len(pts)
    n0 = P + len(lines)
    edges0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
    if spread is None:
        return _blow_generic(n0, edges0, deadline, rng, nprng)
    # Lines: a full spread, each point on exactly one blown line (degree q+2 = d).
    S_lines = [P + j for j in spread]
    # Points: a partial ovoid (no two blown points on a common line), searched.
    S_pts = _ils(P, lines, deadline, rng, nprng)
    return _blow(n0, edges0, S_pts + S_lines)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 5.0)
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 8.0:
        if D >= 4:
            res = _blow_wq(q, deadline, rng, nprng)
        else:
            n0, e0 = lib.projective_plane_incidence(q)
            res = _blow_generic(n0, e0, deadline, rng, nprng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
