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
    Returns (n, edges, P).
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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Twin blow-up.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') sharing the same neighbourhood. A vertex u then has degree
# (d-1) + |N(u) ∩ S| where S = {v : v doubled}, so the degree stays <= d iff
# every vertex has at most one neighbour in S. Equivalently, S must contain no
# two vertices at distance 2. Blow-ups keep bipartiteness and diameter.
#
# Distance-2 conflicts join only vertices of the same side, so the point side
# and the line side of a generalized quadrangle are chosen independently.
# ----------------------------------------------------------------------------

class _Stop(Exception):
    """Raised inside the exact-cover search to restart it or stop at the deadline."""


def _spread(line_pts, P, deadline, rng):
    """Randomised exact cover: find a set of pairwise disjoint lines covering all P points.

    A spread of W(q) is an independent set of size P/(q+1) in the line conflict
    graph (two lines conflict when they share a point). It is found by a
    minimum-remaining-values branching search with random restarts.
    Returns a list of line indices, or None if no spread was found in time.
    """

    def rec(cov, chosen, cnt, limit):
        if not cov:
            return True
        cnt[0] += 1
        if cnt[0] > limit or time.monotonic() > deadline:
            raise _Stop()
        c = min(cov, key=lambda x: len(cov[x]))
        cands = list(cov[c])
        if not cands:
            return False
        rng.shuffle(cands)
        for j in cands:
            pts = line_pts[j]
            pset = set(pts)
            removed = set()
            for p in pts:
                removed |= cov[p]
            new = {q: s - removed for q, s in cov.items() if q not in pset}
            chosen.append(j)
            if rec(new, chosen, cnt, limit):
                return True
            chosen.pop()
        return False

    while time.monotonic() < deadline:
        cov = {p: set() for p in range(P)}
        for j, pts in enumerate(line_pts):
            for p in pts:
                cov[p].add(j)
        chosen = []
        cnt = [0]
        try:
            if rec(cov, chosen, cnt, 3000):
                return chosen
        except _Stop:
            continue
    return None


def _independent_set(N, nb, allowed, rng, nprng, deadline):
    """Iterated local search for a large conflict-free set among `allowed` vertices."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    blocked = ~allowed
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
        score[blocked] = np.inf
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
            if v < 0:
                if (tabu > it).any():
                    tabu[:] = 0
                    continue
                break
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


def _conflicts(n0, edges0, d):
    """Adjacency and distance-2 conflict lists, or (None, None) if degrees are not d-1."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None, None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nb = [sorted(s) for s in cs]
    return adj, nb


def _gq_twin(q, d, deadline, rng, nprng):
    """Blow up W(q) incidence graph. Lines side: exact-cover spread. Points side: local search.

    Returns a list of candidate (n, edges) graphs, all with max degree d.
    """
    n0, e0, P = _gq(q)
    out = [(n0, e0)]
    adj, nb = _conflicts(n0, e0, d)
    if adj is None:
        return out

    now = time.monotonic()
    total = max(0.0, deadline - now)

    # Spread on the line side (a maximum independent set of the line conflict graph).
    line_pts = [adj[v] for v in range(P, n0)]
    S_lines_local = _spread(line_pts, P, now + 0.35 * total, rng)
    if S_lines_local is None:
        mask_l = np.zeros(n0, dtype=bool)
        mask_l[P:] = True
        S_lines = _independent_set(n0, nb, mask_l, rng, nprng, now + 0.5 * total)
    else:
        S_lines = [P + j for j in S_lines_local]

    # Partial ovoid on the point side with the remaining time.
    mask_p = np.zeros(n0, dtype=bool)
    mask_p[:P] = True
    S_pts = _independent_set(n0, nb, mask_p, rng, nprng, deadline)

    out.append(_blow(n0, e0, list(S_pts) + list(S_lines)))
    return out


def _blowup(n0, edges0, d, split, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 (used for the D = 3 route)."""
    adj, nb = _conflicts(n0, edges0, d)
    if adj is None:
        return None
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

    side_a = np.zeros(n0, dtype=bool)
    side_a[:split] = True
    side_b = ~side_a

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    S_a = _independent_set(n0, nb, side_a, rng, nprng, mid)
    S_b = _independent_set(n0, nb, side_b, rng, nprng, deadline)
    return _blow(n0, edges0, S_a + S_b)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 2.0)
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
            for n, e in _gq_twin(q, d, deadline, rng, nprng):
                consider(n, e)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, n0 // 2, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
