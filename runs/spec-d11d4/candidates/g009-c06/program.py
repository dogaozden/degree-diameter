import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases: the points-lines incidence graphs of PG(2, q) and W(q).
# Both are biregular with degree q+1 and diameter 3 (PG) or 4 (W).
# ----------------------------------------------------------------------------

def _gq(q):
    """Return (P, lines) for the symplectic generalized quadrangle W(q).

    Points are indexed 0..P-1; each totally isotropic line is a sorted list of point indices.
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
    P_arr = np.array(pts, dtype=np.int64)
    addt = F.add_table
    mult = F.mul_table
    negt = np.array(NEG, dtype=np.int64)

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = np.zeros((P, P), dtype=bool)
    lines = []
    for i in range(P):
        x = pts[i]
        # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2, vectorised over all y.
        t = addt[mult[x[0], P_arr[:, 1]], negt[mult[x[1], P_arr[:, 0]]]]
        s = addt[mult[x[2], P_arr[:, 3]], negt[mult[x[3], P_arr[:, 2]]]]
        iso = addt[t, s] == 0
        cand = np.nonzero(iso & ~covered[i])[0]
        for j in cand:
            j = int(j)
            if j <= i or covered[i, j]:
                continue
            y = pts[j]
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[M[a][x[k]]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            L = sorted(Lset)
            lines.append(L)
            idx = np.array(L, dtype=np.int64)
            covered[np.ix_(idx, idx)] = True
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): degree q+1, diameter 4."""
    P, lines = _gq(q)
    return P + len(lines), [(p, P + j) for j, L in enumerate(lines) for p in L]


# ----------------------------------------------------------------------------
# Maximum independent set in a conflict graph: penalty-based iterated local
# search (adapted from a previously validated routine).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Large set of vertices with no conflicting pair, found before deadline."""
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
        v = int(np.argmin(score))
        return v if np.isfinite(score[v]) else -1

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            v = pick()
            if v >= 0:
                add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


# ----------------------------------------------------------------------------
# Twin blow-up. If every base vertex has degree d-1, replacing a set S of
# vertices by twin pairs (same neighbourhood) keeps every degree <= d iff no
# vertex has two neighbours in S. That is an independent set in the
# distance-2 conflict graph. Blow-ups keep bipartiteness and diameter.
# For W(q) this gives points forming a partial ovoid and lines forming a
# partial spread, using the same spare slot per vertex.
# ----------------------------------------------------------------------------

def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies with the same neighbourhood."""
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
    """Blow up a base graph of degree d-1 by a large distance-2-free set."""
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
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Diameter-3 base: PG(2, d-1), degree d, when d-1 is a prime power.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Diameter-4 base: W(d-1), degree d, when d-1 is a prime power.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 9:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q and lib.is_prime_power(q) and time.monotonic() < deadline - 1.0:
        try:
            n0 = e0 = None
            if D >= 4 and q <= 9:
                P, lines = _gq(q)
                n0 = P + len(lines)
                e0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
            elif D >= 3 and q <= 11:
                n0, e0 = lib.projective_plane_incidence(q)
            if n0 is not None:
                consider(n0, e0)
                res = _blowup(n0, e0, d, deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
