import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Small deterministic fallbacks: projective plane (D >= 3), Araujo-Pardo-Lopez
# (D = 3), generalized quadrangle W(q) (D >= 4). Every candidate is validated.
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

    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            try:
                return _gq_w(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# NEW FAMILY (D >= 5): bi-Cayley graphs over finite groups of order G, found by
# tabu search instead of annealing.
#
# Vertices A_x = x and B_y = G + y. Connection set S = {s_1..s_d} (distinct).
# Edges A_x ~ B_{x*s} for all x in G, s in S. Left multiplication is an
# automorphism, so the graph is valid iff A_1 and B_1 both reach every vertex
# within D steps. The cost is the number of unreached vertices from those two
# sources; cost 0 is a valid d-regular bipartite graph on 2G vertices.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_table(p):
    """Multiplication table of AGL(1,p); element code (u-1)*p + b encodes x -> u x + b."""
    order = p * (p - 1)
    x = np.arange(order, dtype=np.int64)
    U = x // p + 1
    B = x % p
    prod_u = (U[:, None] * U[None, :]) % p
    M = (prod_u - 1) * p + (U[:, None] * B[None, :] + B[:, None]) % p
    return order, M.astype(np.int64)


def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k (element a*k+b); (a,b)(c,d) = (a + r^b c, b + d)."""
    order = m * k
    x = np.arange(order, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return order, M.astype(np.int64)


def _make_table(spec):
    if spec[0] == "aff":
        return _affine_table(spec[1])
    _, m, k, r = spec
    return _semidirect_table(m, k, r)


def _group_specs(lo, hi, rng):
    """Group specs with order in [lo, hi]: affine groups and semidirect products (r = 1 is abelian)."""
    specs = []
    for p in range(3, hi + 2):
        if _is_prime(p) and lo <= p * (p - 1) <= hi:
            specs.append((p * (p - 1), ("aff", p)))
    for o in range(max(lo, 4), hi + 1):
        for k in range(1, o + 1):
            if o % k:
                continue
            m = o // k
            if m < 2:
                continue
            specs.append((o, ("sd", m, k, 1)))
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if len(rs) > 2:
                rs = rng.sample(rs, 2)
            for r in rs:
                specs.append((o, ("sd", m, k, r)))
    rng.shuffle(specs)
    return specs


def _identity_ok(M):
    G = M.shape[0]
    ar = np.arange(G)
    return bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))


def _bc_adj(M, inv, S, G):
    """Adjacency array (2G, d): A-row x lists G + M[x,s]; B-row y lists M[y, s^-1]."""
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _bc_cost(adj, G, D):
    """Unreached-vertex count from A_1 (node 0) and B_1 (node G) within D steps. Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
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
        total += N - int(np.count_nonzero(seen))
    return total


def _tabu(M, inv, G, d, D, deadline, rng, tenure=12, sample=40, stall_limit=250):
    """Tabu search over connection sets S of size d. Returns (best_cost, best_S)."""
    S = rng.sample(range(G), d)
    c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
    best_c, best_S = c, list(S)
    tabu = {}
    it = 0
    stall = 0
    while best_c > 0 and time.monotonic() < deadline:
        it += 1
        move = None
        for _ in range(sample):
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T = list(S)
            T[i] = x
            c2 = _bc_cost(_bc_adj(M, inv, T, G), G, D)
            if tabu.get((i, x), 0) > it and c2 >= best_c:
                continue
            if move is None or c2 < move[0]:
                move = (c2, i, x, T)
        if move is None:
            continue
        c2, i, x, T = move
        tabu[(i, S[i])] = it + tenure
        S = T
        if c2 < best_c:
            best_c, best_S = c2, list(S)
            stall = 0
        else:
            stall += 1
            if stall > stall_limit:
                break
    return best_c, best_S


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _bicayley_search(d, D, lo, hi, deadline, rng, accept, best_n):
    """Sweep group orders upward from lo in windows; tabu-search each group with a small budget."""
    budget = 1.2
    cur = lo
    while time.monotonic() < deadline and cur <= hi:
        specs = _group_specs(cur, min(hi, cur + 79), rng)
        for o, spec in specs:
            if time.monotonic() >= deadline:
                return best_n
            if 2 * o <= best_n:
                continue
            try:
                order, M = _make_table(spec)
            except Exception:
                continue
            if order != o or not _identity_ok(M):
                continue
            inv = np.argmax(M == 0, axis=1)
            sub = min(deadline, time.monotonic() + budget)
            while time.monotonic() < sub:
                c, S = _tabu(M, inv, order, d, D, sub, rng)
                if c == 0:
                    n, e = _bc_edges(M, S, order)
                    if accept(n, e):
                        best_n = n
                    break
        cur += 80
    return best_n


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 5:
        moore_half = lib.moore_bound(d, D) // 2
        lo = max(best_n // 2 + 1, int(0.44 * moore_half), d + 1)
        _bicayley_search(d, D, lo, moore_half, deadline, rng, consider, best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
