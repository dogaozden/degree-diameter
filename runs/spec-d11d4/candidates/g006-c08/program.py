import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent bases (kept as the safe route): PG(2, q) incidence and the symplectic
# generalized quadrangle W(q), plus the twin blow-up of a degree-(d-1) base.
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
# NEW ROUTE (bold, high-risk): bipartite voltage lifts over non-cyclic groups
# Z_m x|_r Z_k, found by hill climbing directly on the diameter-4 objective.
#
# Base: s vertices on side A and s on side B, each with exactly d darts. A dart
# (a, b, g) lifts to edges (a,x)-(b, x*g). The lift is bipartite, has degree d,
# and G = Z_m x| Z_k acts regularly on each fibre by left multiplication, so
# diameter <= 4 only has to be checked from the 2s identity copies.
#
# Caveat: for a random lift the 3-step ball on the opposite side covers only
# about 1 - exp(-(d-1+(d-1)^2 * ...)/side) of it, so reaching n near the Moore
# bound needs algebraic structure that random search is unlikely to find. The
# route is a best-effort experiment. Every candidate passes lib.is_valid before
# it is accepted, and the parent's graph is the fallback.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a, b) coded a*k+b (identity 0)."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    A, B = x // k, x % k
    MUL = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    INV = np.argmax(MUL == 0, axis=1).astype(np.int64)
    return MUL, INV


def _group_params(G, rng):
    """Semidirect parameters (m, k, r) with m*k = G, r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        if m == 1:
            out.append((1, k, 0))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if not rs:
            continue
        out.append((m, k, 1))                      # abelian Z_m x Z_k
        others = [r for r in rs if r != 1]
        if others:
            out.append((m, k, rng.choice(others)))  # one non-abelian option
    return out


def _lift_search(s, d, G, params, rng, nprng, max_evals, deadline):
    """Hill-climb a degree-d bipartite group lift with 2s base vertices.

    Returns (n, edges) if the lift has diameter <= 4, else None.
    """
    m, k, r = params
    MUL, INV = _group_table(m, k, r)
    E = s * d
    N = 2 * s * G
    A_idx = np.arange(E, dtype=np.int64) // d
    B = nprng.permutation(np.repeat(np.arange(s, dtype=np.int64), d))
    g = nprng.integers(0, G, size=E).astype(np.int64)
    nsrc = 2 * s
    srcs = np.concatenate([np.arange(s) * G, s * G + np.arange(s) * G]).astype(np.int64)

    def build(B, g):
        # A copies a*G+x have neighbours B-copies (s*G + b*G + x*g).
        T1 = (s * G + B[:, None] * G) + MUL[:, g].T
        nbrA = T1.reshape(s, d, G).transpose(0, 2, 1).reshape(s * G, d)
        # B copies s*G+b*G+y have neighbours A-copies a*G + y*g^{-1}.
        order = np.argsort(B, kind='stable').reshape(s, d)
        T2 = A_idx[:, None] * G + MUL[:, INV[g]].T
        nbrB = T2[order].transpose(0, 2, 1).reshape(s * G, d)
        return np.vstack([nbrA, nbrB])

    def score(nbr):
        R = np.zeros((nsrc, N), dtype=bool)
        R[np.arange(nsrc), srcs] = True
        for _ in range(4):
            R2 = R.copy()
            for c in range(d):
                R2 |= R[:, nbr[:, c]]
            R = R2
        return nsrc * N - int(R.sum())

    cur_nbr = build(B, g)
    cur = score(cur_nbr)
    evals = 0
    while cur > 0 and evals < max_evals:
        if (evals & 31) == 0 and time.monotonic() >= deadline:
            break
        evals += 1
        B2, g2 = B.copy(), g.copy()
        if rng.random() < 0.5:
            j = rng.randrange(E)
            g2[j] = rng.randrange(G)
        else:
            j, l = rng.randrange(E), rng.randrange(E)
            if B2[j] == B2[l]:
                continue
            B2[j], B2[l] = B2[l], B2[j]      # degree-preserving endpoint swap
        nb = build(B2, g2)
        sc = score(nb)
        if sc <= cur:
            B, g, cur, cur_nbr = B2, g2, sc, nb
    if cur > 0:
        return None
    edges = set()
    for i in range(s * G):
        for v in cur_nbr[i]:
            edges.add((i, int(v)))
    return N, sorted(edges)


def _search_route(d, lo, hi, consider, best_n_fn, deadline, rng, nprng):
    """Try group-lift candidates in ascending order of order n within [lo, hi]."""
    cands = []
    for s in (1, 2, 3, 4):
        Gmin = max(1, -(-lo // (2 * s)))
        Gmax = hi // (2 * s)
        for G in range(Gmin, Gmax + 1):
            for params in _group_params(G, rng):
                cands.append((2 * s * G, s, G, params))
    rng.shuffle(cands)
    cands.sort(key=lambda c: c[0])
    for n, s, G, params in cands:
        if time.monotonic() >= deadline:
            break
        if n <= best_n_fn():
            continue
        res = _lift_search(s, d, G, params, rng, nprng, 1500, deadline)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Parent blow-up route, given a shorter share of the budget so the new route runs.
    parent_deadline = start + max(0.5, 0.4 * time_limit)
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < parent_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, parent_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # New bold route: non-cyclic group lifts for diameter 4, with the rest of the budget.
    if D == 4 and d >= 4:
        search_deadline = start + 0.85 * time_limit - 2.0
        try:
            hi = lib._moore_bound(d, D)
            _search_route(d, best_n + 1, hi, consider, lambda: best_n,
                          search_deadline, rng, nprng)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
