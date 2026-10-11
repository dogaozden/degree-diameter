import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
# New bold arm: single-base Haar-type bi-Cayley graphs over groups
# Z_m x| Z_k2.  Vertices A_g = g and B_h = G + h.  A_g ~ B_{g*s} for s in S,
# |S| = d.  Left multiplication is an automorphism that is transitive on each
# side, so diameter <= D is equivalent to: BFS from A_e and from B_e both reach
# all 2G vertices within D steps.  Search runs simulated annealing over S.
# ----------------------------------------------------------------------------

_K2S = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24, 28, 30, 36, 42, 48)


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = g with g*s = h, for Z_m x| Z_k2."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _group_candidates(T, span, rng):
    """Groups (G, m, k2, r) with G in [T, T + span*k2]; a few random valid r per (m, k2)."""
    out = []
    for k2 in _K2S:
        m0 = max(2, -(-T // k2))
        for m in range(m0, m0 + span + 1):
            G = m * k2
            if G < T:
                continue
            rs = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not rs:
                continue
            for c in rng.sample(rs, min(3, len(rs))):
                out.append((G, m, k2, c))
    return out


def _reach(adj, src, D, N):
    """Number of vertices within distance D of src (BFS over numpy adjacency rows)."""
    seen = np.zeros(N, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = adj[frontier].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        frontier = nb
    return int(seen.sum())


def _haar_search(d, D, G, Ts, Invs, rng, deadline, max_iter):
    """Simulated annealing over connection sets S (|S| = d). Returns list S or None."""
    N = 2 * G
    S = rng.sample(range(G), d)
    inS = set(S)
    adj = np.empty((N, d), dtype=np.int64)
    adj[:G] = G + Ts[S].T
    adj[G:] = Invs[S].T

    def cost():
        return (N - _reach(adj, 0, D, N)) + (N - _reach(adj, G, D, N))

    cur = cost()
    best_c, best_S = cur, list(S)
    T0 = 1.0
    it = 0
    while cur > 0 and it < max_iter and time.monotonic() < deadline:
        temp = max(0.05, T0 * (1.0 - it / max_iter))
        it += 1
        j = rng.randrange(d)
        old = S[j]
        new = rng.randrange(G)
        while new in inS:
            new = rng.randrange(G)
        S[j] = new
        adj[:G, j] = G + Ts[new]
        adj[G:, j] = Invs[new]
        c2 = cost()
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            inS.discard(old)
            inS.add(new)
            cur = c2
            if cur < best_c:
                best_c, best_S = cur, list(S)
        else:
            S[j] = old
            adj[:G, j] = G + Ts[old]
            adj[G:, j] = Invs[old]
    return list(best_S) if best_c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold arm: Haar-type bi-Cayley search over groups of order just above the record.
    cache = {}
    while time.monotonic() < deadline:
        T = best_n // 2 + 1 + rng.randrange(0, 6)
        if T not in cache:
            cache[T] = _group_candidates(T, 12, rng)
        cands = cache[T]
        if not cands:
            continue
        if rng.random() < 0.7:
            minG = min(c[0] for c in cands)
            pool = [c for c in cands if c[0] == minG]
        else:
            pool = cands
        G, m, k2, r = rng.choice(pool)
        Gt, Ts, Invs = _semidirect_tables(m, k2, r)
        slice_end = min(deadline, time.monotonic() + rng.uniform(2.0, 6.0))
        S = _haar_search(d, D, Gt, Ts, Invs, rng, slice_end, 20000)
        if S is not None:
            edges = [(g, Gt + int(Ts[s, g])) for g in range(Gt) for s in S]
            consider(2 * Gt, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
