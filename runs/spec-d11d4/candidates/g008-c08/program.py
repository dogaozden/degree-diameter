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


def _nonsquare(F, q):
    """A non-square of GF(q) for odd q, or None."""
    squares = {F.mul(x, x) for x in range(1, q)}
    for r in range(1, q):
        if r not in squares:
            return r
    return None


def _spread_ids(q, r, A, M, norm, index, lines):
    """Line indices of a spread of W(q), built from GF(q^2) = GF(q)[t]/(t^2 - r).

    For odd q and the form Re(z1*w2) - Re(z2*w1) (with z = x0 + x1 t, z2 = x2 + x3 t),
    the lines {mu*(z1, z2) : mu in GF(q^2)*} are totally isotropic and partition the
    points. Returns None if anything does not check out.
    """
    def m2(p, z):
        return (A[M[p[0]][z[0]]][M[r][M[p[1]][z[1]]]],
                A[M[p[0]][z[1]]][M[p[1]][z[0]]])

    units = [(a, b) for a in range(q) for b in range(q) if a or b]
    reps = [((1, 0), (s0, s1)) for s0 in range(q) for s1 in range(q)]
    reps.append(((0, 0), (1, 0)))
    line_index = {tuple(L): j for j, L in enumerate(lines)}
    out = []
    seen = set()
    for z1, z2 in reps:
        pset = set()
        for mu in units:
            w1 = m2(mu, z1)
            w2 = m2(mu, z2)
            pset.add(index[norm((w1[0], w1[1], w2[0], w2[1]))])
        key = tuple(sorted(pset))
        if len(key) != q + 1 or key not in line_index:
            return None
        for p in key:
            if p in seen:
                return None
            seen.add(p)
        out.append(line_index[key])
    if len(out) != q * q + 1:
        return None
    return out


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Returns (n, edges, P, spread), where
    spread is a list of base line indices forming a spread (odd q), or None.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    r = _nonsquare(F, q) if q % 2 == 1 else None
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    if r is None:
        def orth(x, y):
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            return A[t][s] == 0
    else:
        # Form Re(z1 w2) - Re(z2 w1) over GF(q^2), symplectic, equivalent to W(q).
        def orth(x, y):
            t = A[M[x[0]][y[2]]][NEG[M[x[2]][y[0]]]]
            s = A[M[x[1]][y[3]]][NEG[M[x[3]][y[1]]]]
            return A[t][M[r][s]] == 0

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            if not orth(x, y):
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
                for rr in L:
                    cp[rr] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    spread = None
    if r is not None:
        spread = _spread_ids(q, r, A, M, norm, index, lines)
    return P + len(lines), edges, P, spread


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every base vertex has degree d-1, blowing up a set S of base vertices into
# twin pairs keeps degrees <= d iff every vertex has at most one S-neighbour.
# For W(q), this means: S-points pairwise non-collinear (partial ovoid) and
# S-lines pairwise disjoint (partial spread). The two kinds never conflict.
# A full spread of W(q) has q^2+1 lines and always exists, so we take it
# explicitly and search only for the point part.
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


def _blowup(n0, edges0, d, deadline, rng, nprng, P=None, spread=None):
    """Twin blow-up of a base graph of degree d-1 by a distance-2-free set."""
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
    if spread is not None and P is not None:
        # Spread lines are fixed (each point has exactly one S-line, lines pairwise
        # disjoint). Search only the point part: a partial ovoid.
        S_pts = _independent_set(P, nb[:P], rng, nprng, deadline)
        S = list(S_pts) + [P + j for j in spread]
    else:
        if n0 <= 60:
            deadline = min(deadline, time.monotonic() + 2.0)
        S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


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

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        P = None
        spread = None
        if D >= 4:
            n0, e0, P, spread = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng, P, spread)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
