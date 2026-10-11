import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured families kept from the parent: PG(2,q) incidence, Araujo-Pardo-Lopez
# for D = 3, and the generalized quadrangle W(q) for D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over non-cyclic groups Z_m x|_r Z_k2.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, with G = m*k2 and
# g, h group elements. Layer L pairs each A_i with B_{P[L][i]} through a voltage
# S[L][i]: A_{i,g} ~ B_{j, g*s}. Each layer is a permutation of the k A-orbits,
# so every vertex has degree d, and the graph is bipartite automatically.
#
# Left multiplication by x is an automorphism, so the diameter test only needs
# BFS from the 2k representatives A_{i,e} and B_{j,e}. A cost of zero means the
# graph is valid. This is a different search space from the parent's version:
# it uses the full family of groups Z_m x|_r Z_k2 with a vectorized BFS.
# ----------------------------------------------------------------------------

def _divisor_pairs(G):
    return [(m, G // m) for m in range(1, G + 1) if G % m == 0]


def _pick_r(m, k2, rng):
    """Return r with gcd(r, m) = 1 and r^k2 = 1 mod m (r = 1 always works when m > 1)."""
    if m == 1:
        return 0
    for _ in range(60):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return r
    return 1


def _group_tables(m, k2, r):
    """Right-multiplication table T[x, y] = x*y and right inverses, for Z_m x|_r Z_k2.

    Element x = a*k2 + b codes (a, b). Product (a, b)(c, d) = (a + r^b c, b + d).
    The identity is element 0.
    """
    G = m * k2
    idx = np.arange(G, dtype=np.int64)
    A = idx // k2
    B = idx % k2
    pw = np.array([pow(r, b, m) if m > 1 else 0 for b in range(k2)], dtype=np.int64)
    rb = pw[B]
    MA = (A[:, None] + rb[:, None] * A[None, :]) % m
    MB = (B[:, None] + B[None, :]) % k2
    T = MA * k2 + MB
    inv = np.argmax(T == 0, axis=1)
    return T, inv


def _dup_free(k, d, P, S):
    """True if no two darts share the same (A-orbit, B-orbit, voltage) triple."""
    keys = set()
    for L in range(d):
        for i in range(k):
            key = (i, P[L][i], S[L][i])
            if key in keys:
                return False
            keys.add(key)
    return True


def _build_nbr(k, G, d, T, inv, P, S):
    """Neighbour array of shape (2kG, d): column L holds the layer-L neighbour of each vertex."""
    N = 2 * k * G
    nbr = np.empty((N, d), dtype=np.int64)
    ar = np.arange(G, dtype=np.int64)
    for L in range(d):
        Pl = P[L]
        Sl = S[L]
        Pinv = [0] * k
        for i, j in enumerate(Pl):
            Pinv[j] = i
        for i in range(k):
            j = Pl[i]
            s = Sl[i]
            nbr[i * G:(i + 1) * G, L] = (k + j) * G + T[ar, s]
        for j in range(k):
            i = Pinv[j]
            s = Sl[i]
            nbr[(k + j) * G:(k + j + 1) * G, L] = i * G + T[ar, inv[s]]
    return nbr


def _unreached(N, nbr, reps, D):
    """Total count of (representative, vertex) pairs at distance > D."""
    total = 0
    for src in reps:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(seen.sum())
    return total


def _anneal(d, D, k, G, T, inv, rng, deadline, max_iters):
    """Anneal voltages and layer permutations. Returns (n, edges) on success, else None."""
    N = 2 * k * G
    reps = [x * G for x in range(2 * k)]
    P = S = None
    for _ in range(200):
        P = [rng.sample(range(k), k) for _ in range(d)]
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        if _dup_free(k, d, P, S):
            break
    else:
        return None

    nbr = _build_nbr(k, G, d, T, inv, P, S)
    cost = _unreached(N, nbr, reps, D)
    temp = 10.0
    it = 0
    while cost > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        temp = max(0.3, temp * 0.998)
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            kind = 0
            i = rng.randrange(k)
            old = S[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[L][i] = new
        else:
            kind = 1
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]

        if _dup_free(k, d, P, S):
            nbr2 = _build_nbr(k, G, d, T, inv, P, S)
            c2 = _unreached(N, nbr2, reps, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, nbr = c2, nbr2
                continue

        # Reject: undo the move.
        if kind == 0:
            S[L][i] = old
        else:
            P[L][a], P[L][b] = P[L][b], P[L][a]

    if cost != 0:
        return None
    E = set()
    for x in range(k * G):
        for y in nbr[x]:
            E.add((x, int(y)))
    return N, sorted(E)


def _search_gen(d, D, rng, deadline, get_best):
    """Yield valid bi-Cayley graphs, aiming for orders above the current best."""
    while time.monotonic() < deadline:
        best_n = get_best()
        k = rng.choice([1, 1, 2, 2, 3, 4])
        g_min = best_n // (2 * k) + 1
        if g_min < d:
            g_min = d
        G = rng.randint(g_min, g_min + max(3, g_min // 6))
        m, k2 = rng.choice(_divisor_pairs(G))
        r = _pick_r(m, k2, rng)
        T, inv = _group_tables(m, k2, r)
        budget = min(deadline, time.monotonic() + 6.0)
        res = _anneal(d, D, k, G, T, inv, rng, budget, 1500)
        if res is not None:
            yield res


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, fb_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for all D >= 2: bi-Cayley lifts over non-cyclic groups.
    if d >= 2:
        try:
            for n_c, e_c in _search_gen(d, D, rng, deadline, lambda: best[0]):
                consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = [fb_n, fb_e]
    return best[0], best[1]
